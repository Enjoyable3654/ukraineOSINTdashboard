#!/usr/bin/env python3
"""
ALL daily data updates live in this one file.

  python update.py                        run every enabled source, save into data/<today>/
  python update.py --only deepstate       run just one source
  python update.py --inspect deepstate    print what one source returns; saves nothing

HOW TO ADD A SOURCE: copy the "deepstate" block in SOURCES below, give it a new name, and change its address and
rules. A source that returns map polygons ("kind": "occupation") needs nothing else. Other kinds (points, posts)
get their own function in the CODE section and an entry in KINDS.

Nothing is dropped silently: polygons that match no rule are kept as category "unmapped", and non-polygon items
are counted in the run log (data/<day>/meta.json). One failing source never stops the others, and a failed run
never overwrites good data.
"""
import argparse, collections, datetime as dt, gzip, json, math, re, shutil, sys, time, urllib.request
from pathlib import Path

try:
    from shapely.geometry import shape, mapping
    from shapely.ops import unary_union
    HAVE_SHAPELY = True
except ImportError:  # still runs, but polygons are not merged or simplified
    HAVE_SHAPELY = False

ROOT = Path(__file__).resolve().parent

# =====================================================================================================
# SETTINGS (edit this part)
# =====================================================================================================

USER_AGENT = "ukraine-osint-dashboard/1.0 (+https://github.com/Enjoyable3654/ukraineOSINTdashboard)"

CATEGORIES = {   # shared by all sources; the map's checkboxes use these
    "ukraine":   {"label": "Ukraine-controlled / recently liberated", "color": "#2a7de1"},
    "russia":    {"label": "Russian-occupied", "color": "#d64545"},
    "contested": {"label": "Contested / unknown status", "color": "#e0a800"},
    "claims":    {"label": "Claimed by a party (unverified)", "color": "#8e5bd0"},
    "other":     {"label": "Other", "color": "#7f8c8d"},
    "unmapped":  {"label": "Unmapped source type (needs a rule)", "color": "#444444"},
}

SOURCES = {
    "deepstate": {
        "enabled": True,
        "kind": "occupation",
        "name": "DeepStateMap",
        "url": "https://deepstatemap.live/en",
        "endpoint": "https://deepstatemap.live/api/history/last",   # confirmed working from a real inspect run
        "name_separator": "///",      # DeepState names look like "<Ukrainian> /// <English> /// <stable code>"
        "name_part": 1,               # keep the English part (for display: popups, source_labels)
        "classify_part": 2,           # match rules against the stable code instead (does not change with wording)
        "simplify_degrees": 0.0001,   # about 11 m; raise it if files get too big
        "cleanup_buffer_degrees": 0.00001,   # about 1 m, closes hairline seams after merging
        # First matching rule wins. Anything matching nothing becomes "unmapped" and is still shown.
        # Confirmed from a real inspect run against DeepState's own codes (2026-09-26).
        # "other" = DeepState's other Russian territorial claims not part of the Ukraine war
        # (Abkhazia, Tskhinvali/South Ossetia, Kuril Islands, Baltic border districts, Finland's
        # Petsamo/Salla, Chechnya/Ichkeria, Karelia, East Prussia, Transnistria). Kept, not hidden,
        # but shown separately so they are never mixed into the Ukraine-occupation shape.
        "rules": [
            {"category": "russia",    "regex": "status\\.occupied|territories\\.(crimea|ordlo|tuzla)"},
            {"category": "ukraine",   "regex": "status\\.dismissed|zmiinyi_island"},
            {"category": "contested", "regex": "status\\.unknown"},
            {"category": "other",     "regex": "territories\\."},
        ],
    },
    # "another_source": { ...copy the block above and change it... },
}

# =====================================================================================================
# CODE (you should not need to touch this)
# =====================================================================================================

class SourceError(Exception):
    pass


def fetch(url, tries=4, wait=4):
    """Download JSON, retrying with growing pauses (4, 8, 16 s). Sends an honest, identifying User-Agent."""
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
            with urllib.request.urlopen(req, timeout=60) as r:
                return json.loads(r.read().decode("utf-8"))
        except Exception as e:
            print(f"  attempt {i + 1}/{tries} failed: {e}", file=sys.stderr)
            if i == tries - 1:
                raise
            time.sleep(wait)
            wait *= 2


def find_feature_collection(node):
    """The response may wrap the GeoJSON inside other keys, so search for it."""
    if isinstance(node, dict):
        if node.get("type") == "FeatureCollection" and isinstance(node.get("features"), list):
            return node
        node = list(node.values())
    if isinstance(node, list):
        for v in node:
            found = find_feature_collection(v)
            if found:
                return found
    return None


def name_parts(props, sep):
    raw = str(props.get("name") or "").strip()
    if sep and sep in raw:
        return [p.strip() for p in raw.split(sep)]
    return [raw] if raw else []


def label_of(props, cfg):
    """Human-readable label, for display (popups, source_labels)."""
    parts = name_parts(props, cfg.get("name_separator"))
    i = cfg.get("name_part", 1)
    if parts:
        return parts[i] if i < len(parts) else parts[-1]
    return str(props.get("fill") or "(no label)")


def classify_key(props, cfg):
    """Text matched against category rules. Some sources put a stable machine code in a separate
    part of the name (set "classify_part" to its index) that will not change even if the source
    rewords its display text; falls back to the display label if there is no such part."""
    parts = name_parts(props, cfg.get("name_separator"))
    i = cfg.get("classify_part", cfg.get("name_part", 1))
    if parts:
        return parts[i] if i < len(parts) else parts[-1]
    return label_of(props, cfg)


def classify(label, props, rules):
    for r in rules:
        if "names" in r and label.lower() not in [n.lower() for n in r["names"]]:
            continue
        if "regex" in r and not re.search(r["regex"], label, re.I):
            continue
        if any(props.get(k) != v for k, v in r.get("props", {}).items()):
            continue
        return r["category"]
    return "unmapped"


def xy(c):
    """Keep only [lon, lat] (drop any height value) and round to about 1 m."""
    if isinstance(c[0], (int, float)):
        return [round(c[0], 5), round(c[1], 5)]
    return [xy(x) for x in c]


def to_polygons(g):
    t = g.get("type")
    if t == "Polygon":
        return [xy(g["coordinates"])]
    if t == "MultiPolygon":
        return [xy(p) for p in g["coordinates"]]
    return []


def ring_area_km2(ring):
    R, total = 6371.0088, 0.0
    for (x1, y1), (x2, y2) in zip(ring, ring[1:]):
        total += math.radians(x2 - x1) * (2 + math.sin(math.radians(y1)) + math.sin(math.radians(y2)))
    return abs(total) * R * R / 2


def polygons_area_km2(polys):
    return sum(ring_area_km2(p[0]) - sum(ring_area_km2(h) for h in p[1:]) for p in polys)


def dissolve(polys, tol, eps):
    """Merge all polygons of one category into one shape. Returns (geometry, note)."""
    if HAVE_SHAPELY:
        merged = unary_union([shape({"type": "Polygon", "coordinates": p}).buffer(0) for p in polys])
        if eps > 0:
            merged = merged.buffer(eps, quad_segs=1, join_style="mitre").buffer(-eps, quad_segs=1, join_style="mitre")
        if tol > 0:
            merged = merged.simplify(tol, preserve_topology=True)
        g = mapping(merged)
        return {"type": g["type"], "coordinates": xy(g["coordinates"])}, "merged and simplified"
    return {"type": "MultiPolygon", "coordinates": polys}, "NOT merged or simplified (shapely not installed)"


def print_inspect(payload, fc, cfg):
    print("Top-level keys:", list(payload.keys()) if isinstance(payload, dict) else type(payload).__name__)
    print("Features:", len(fc["features"]))
    groups = collections.defaultdict(lambda: [0, 0.0])
    for f in fc["features"]:
        g, props = f.get("geometry") or {}, f.get("properties") or {}
        key = (label_of(props, cfg), classify_key(props, cfg), props.get("fill"), props.get("stroke"), g.get("type"))
        groups[key][0] += 1
        groups[key][1] += polygons_area_km2(to_polygons(g))
    print("\nEach distinct type found (label | match-key | fill | stroke | shape): count, approx km2 -> category it would get")
    for (label, ckey, fill, stroke, gt), (n, area) in sorted(groups.items(), key=lambda kv: -kv[1][1]):
        cat = classify(ckey, {"fill": fill, "stroke": stroke}, cfg["rules"]) if gt in ("Polygon", "MultiPolygon") else "(not a polygon, ignored)"
        print(f"  {label} | {ckey} | {fill} | {stroke} | {gt}: {n}, {area:,.0f} -> {cat}")
    sample = next((f.get("properties") for f in fc["features"] if f.get("properties")), None)
    print("\nExample of one feature's raw properties:", json.dumps(sample, ensure_ascii=False)[:600])


def read_json(path, default):
    return json.loads(path.read_text("utf-8")) if path.exists() else default


def write_json(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=False, separators=(",", ":")), "utf-8")


def run_occupation(sid, cfg, args, day, now, data):
    """A source that returns map polygons: sort into categories, merge, save polygons/occupation.geojson."""
    try:
        payload = json.load(open(args.from_file, encoding="utf-8")) if args.from_file else fetch(cfg["endpoint"])
    except Exception as e:
        raise SourceError(f"could not get data from {args.from_file or cfg['endpoint']}: {e}")
    fc = find_feature_collection(payload)
    if not fc:
        raise SourceError("no GeoJSON FeatureCollection found in the response. Run --inspect and send the output to Claude.")
    if args.inspect:
        return print_inspect(payload, fc, cfg)

    snap = payload.get("datetime") if isinstance(payload, dict) and isinstance(payload.get("datetime"), str) else None
    polys, labels, skipped, n_feat = collections.defaultdict(list), collections.defaultdict(set), collections.Counter(), collections.Counter()
    for f in fc["features"]:
        g, props = f.get("geometry") or {}, f.get("properties") or {}
        parts = to_polygons(g)
        if not parts:
            skipped[str(g.get("type"))] += 1
            continue
        label = label_of(props, cfg)
        cat = classify(classify_key(props, cfg), props, cfg["rules"])
        polys[cat].extend(parts)
        labels[cat].add(label)
        n_feat[cat] += 1
    if not polys:
        raise SourceError("the response contained no polygons; nothing saved (existing data left untouched).")

    features, by_cat, note = [], {}, ""
    for cat, plist in polys.items():
        geom, note = dissolve(plist, cfg["simplify_degrees"], cfg.get("cleanup_buffer_degrees", 0))
        area = polygons_area_km2(geom["coordinates"] if geom["type"] == "MultiPolygon" else [geom["coordinates"]])
        by_cat[cat] = {"source_polygons": n_feat[cat], "area_km2_approx": round(area)}
        features.append({"type": "Feature", "geometry": geom, "properties": {
            "source": sid, "source_name": cfg["name"], "source_url": cfg["url"],
            "category": cat, "category_label": CATEGORIES.get(cat, {}).get("label", cat),
            "snapshot_time": snap, "fetched_at_utc": now.isoformat(timespec="seconds"),
            "source_labels": sorted(labels[cat]), "source_polygons": n_feat[cat],
            "area_km2_approx": round(area), "processing": note}})

    # Write to a working folder first, and only move the finished file into data/ once it is complete.
    # If anything above raises an exception, nothing here runs, so a half-built file never reaches data/
    # and a day already saved from an earlier successful run is left untouched.
    filename = KIND_FILENAMES[cfg["kind"]]
    work_path = args.working_dir_path / day / sid / filename
    write_json(work_path, {"type": "FeatureCollection", "features": features})
    final_path = data / day / sid / filename
    try:
        final_path.parent.mkdir(parents=True, exist_ok=True)
        if final_path.exists():
            final_path.unlink()
        shutil.move(str(work_path), str(final_path))
    except Exception as e:
        raise SourceError(f"built the data but could not move it into place: {e}")

    save_meta(data, day, sid, {
        "status": "ok", "fetched_at_utc": now.isoformat(timespec="seconds"), "snapshot_time": snap,
        "endpoint": args.from_file or cfg["endpoint"], "files": [f"{sid}/{filename}"], "by_category": by_cat,
        "unmapped_labels": sorted(labels.get("unmapped", [])), "skipped_non_polygon": dict(skipped), "processing": note})
    if args.keep_raw:
        with gzip.open(data / day / sid / "raw.json.gz", "wt", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False)

    print(f"[{sid}] saved {final_path}  ({note})")
    for cat, v in by_cat.items():
        print(f"  {cat}: {v['source_polygons']} source polygons, about {v['area_km2_approx']:,} km2")
    if "unmapped" in by_cat:
        print("  WARNING: some types matched no rule:", "; ".join(sorted(labels["unmapped"])))
    if skipped:
        print("  Ignored non-polygon items:", dict(skipped))


KINDS = {"occupation": run_occupation}   # add new kinds of source here
# Output file for each kind, saved as data/<day>/<source>/<data type>/<specific data>.geojson.
# meta.json lists each source's files, and the dashboard reads them from there.
KIND_FILENAMES = {"occupation": "polygons/occupation.geojson"}


def save_meta(data, day, sid, entry):
    path = data / day / "meta.json"
    meta = read_json(path, {"date": day, "sources": {}})
    meta["sources"][sid] = entry
    write_json(path, meta)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inspect", metavar="SOURCE")
    ap.add_argument("--only", metavar="SOURCE")
    ap.add_argument("--from-file", help="use a saved response instead of the network (testing; needs --only)")
    ap.add_argument("--date", help="folder date YYYY-MM-DD (default: today, UTC)")
    ap.add_argument("--data-dir", default=str(ROOT / "data"))
    ap.add_argument("--working-dir", default=str(ROOT / "data_working"), help="scratch space; never committed, cleared after each run")
    ap.add_argument("--keep-raw", action="store_true", help="also save the raw response as .json.gz (large)")
    args = ap.parse_args()

    if args.inspect:
        ids = [args.inspect]
    elif args.only:
        ids = [args.only]
    else:
        ids = [k for k, v in SOURCES.items() if v.get("enabled", True)]
    for sid in ids:
        if sid not in SOURCES:
            sys.exit(f"ERROR: unknown source '{sid}'. Known sources: {', '.join(SOURCES)}")

    now = dt.datetime.now(dt.timezone.utc)
    day = args.date or now.strftime("%Y-%m-%d")
    data = Path(args.data_dir)
    args.working_dir_path = Path(args.working_dir)
    failed, worked = [], []
    for sid in ids:
        cfg = SOURCES[sid]
        try:
            KINDS[cfg["kind"]](sid, cfg, args, day, now, data)
            worked.append(sid)
        except SourceError as e:
            print(f"[{sid}] FAILED: {e}", file=sys.stderr)
            failed.append(sid)
            if not args.inspect and sid not in read_json(data / day / "meta.json", {"sources": {}})["sources"]:
                save_meta(data, day, sid, {"status": "error", "error": str(e), "at_utc": now.isoformat(timespec="seconds")})

    if worked and not args.inspect:
        write_json(data / "categories.json", {"categories": CATEGORIES})
        # A day "has data" once at least one source folder exists under it (a source only gets a
        # folder once its file has been fully moved into place, so a half-finished run never counts).
        dates = sorted(p.name for p in data.iterdir() if p.is_dir() and any(c.is_dir() for c in p.iterdir()))
        write_json(data / "index.json", {"dates": dates, "updated_utc": now.isoformat(timespec="seconds")})
    shutil.rmtree(args.working_dir_path, ignore_errors=True)   # scratch space only; data/ already has the real copy
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()

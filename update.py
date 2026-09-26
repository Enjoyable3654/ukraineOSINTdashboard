#!/usr/bin/env python3
"""
ALL daily data updates live in this one file.

  python update.py                        run every enabled source, save into data/<today>/
  python update.py --only deepstate       run just one source
  python update.py --inspect deepstate    print what one source returns; saves nothing

HOW TO ADD A SOURCE: copy the "deepstate" block in SOURCES below, give it a new name, and change its address and
rules. Sources that return map polygons ("kind": "occupation" for GeoJSON, "kmz_layers" for dated KMZ files)
need nothing else. "geoconfirmed" saves GeoConfirmed's geolocated events as map points. Other kinds (points, posts) get their own function in the CODE section and an entry in KINDS.

Nothing is dropped silently: polygons that match no rule are kept as category "unmapped", and non-polygon items
are counted in the run log (data/<day>/meta.json). One failing source never stops the others, and a failed run
never overwrites good data.
"""
import argparse, collections, csv, datetime as dt, gzip, io, json, math, re, shutil, sys, time, urllib.parse, urllib.request, zipfile
import xml.etree.ElementTree as ET
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
    "contested": {"label": "Contested / unknown status", "color": "#444444"},
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
    "ukrdaily": {
        "enabled": True,
        "kind": "kmz_layers",
        "name": "UkrDailyUpdate",
        "url": "https://map.ukrdailyupdate.com/",
        # One KMZ file per layer per date. Files appear about 2 days after their date, so each run checks the
        # last "lookback_days" days and saves every date not yet saved, under that date's own folder.
        "endpoint": "https://map.ukrdailyupdate.com/kmz/{date}/{layer}.kmz",
        "layers": ["Ukrainian", "Russians", "Contested Areas"],
        "lookback_days": 7,
        "simplify_degrees": 0.0001,
        "cleanup_buffer_degrees": 0.00001,
        # Matched against "<layer>|<shape colour>" (colour taken from each shape's KMZ style).
        # Confirmed from the real 2026-09-22 files. "background" = whole-country shading (Russia, Belarus,
        # Transnistria; Poland, Romania, Hungary, Slovakia, Moldova, Baltic states): left off the map by the
        # user's decision (2026-09-26), but every left-off shape is listed by name in meta.json.
        "rules": [
            {"category": "ukraine",    "regex": "^Ukrainian\\|(0288D1|01579B)$"},
            {"category": "russia",     "regex": "^Russians\\|FF5252$"},
            {"category": "contested",  "regex": "^Contested Areas\\|FFD600$"},
            {"category": "background", "regex": "^Ukrainian\\|1A237E$|^Russians\\|(A52714|880E4F|C2185B)$"},
        ],
        "leave_off_map": ["background"],
    },
    "geoconfirmed": {
        "enabled": True,
        "kind": "geoconfirmed",
        "name": "GeoConfirmed",
        "url": "https://geoconfirmed.org/map/ukraine",
        "conflict": "Ukraine",
        # Public, no-login API (https://geoconfirmed.org/scalar/v1). Three requests per run:
        # the CSV has each event's text fields; the GeoJSON and icon list give each event's category.
        "csv": "https://geoconfirmed.org/api/Map/export/{conflict}/csv?start={start}&end={end}",
        "geojson": "https://geoconfirmed.org/api/Placemark/{conflict}/geojson",
        "icons": "https://geoconfirmed.org/api/Placemark/{conflict}/icons",
        "placemark_link": "https://geoconfirmed.org/map/ukraine/{id}",
        # Events keep being added for past dates, so each run re-saves the last "lookback_days" days.
        "lookback_days": 7,
    },
    # "another_source": { ...copy a block above and change it... },
}

# =====================================================================================================
# CODE (you should not need to touch this)
# =====================================================================================================

class SourceError(Exception):
    pass


def fetch(url, accept="*/*", tries=4, wait=4):
    """Download a file, retrying with growing pauses (4, 8, 16 s). Sends an honest, identifying User-Agent.
    "Not found" (404) is not retried: it means the file does not exist (yet)."""
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": accept})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read()
        except Exception as e:
            print(f"  attempt {i + 1}/{tries} failed: {e}", file=sys.stderr)
            if i == tries - 1 or getattr(e, "code", None) == 404:
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
        payload = json.load(open(args.from_file, encoding="utf-8")) if args.from_file else json.loads(fetch(cfg["endpoint"], "application/json"))
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
    save_polygons(sid, cfg, args, day, now, data, polys, labels, n_feat, {
        "snapshot_time": snap, "endpoint": args.from_file or cfg["endpoint"], "skipped_non_polygon": dict(skipped)})
    if args.keep_raw:
        with gzip.open(data / day / sid / "raw.json.gz", "wt", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False)


def kml_shapes(kml):
    """For each Placemark in a KML file: (name, colour from its style, list of polygons, non-polygon shape types)."""
    for pm in ET.fromstring(kml).iterfind(".//{*}Placemark"):
        m = re.search(r"[0-9A-Fa-f]{6}", pm.findtext("{*}styleUrl") or "")
        polys = []
        for pg in pm.iterfind(".//{*}Polygon"):
            rings = [pg.find("{*}outerBoundaryIs//{*}coordinates")] + pg.findall("{*}innerBoundaryIs//{*}coordinates")
            polys.append([xy([[float(v) for v in t.split(",")[:2]] for t in r.text.split()]) for r in rings if r is not None])
        other = [t for t in ("Point", "LineString") if pm.find(".//{*}" + t) is not None]
        yield (pm.findtext("{*}name") or "").strip(), m.group(0).upper() if m else "", polys, other


def run_kmz_layers(sid, cfg, args, day, now, data):
    """A source that publishes one KMZ (zipped KML) file per layer per date. Each date is saved in its own
    day folder; dates already saved are skipped unless --date asks for one again."""
    today = dt.date.fromisoformat(day)
    dates = [day] if args.date else [(today - dt.timedelta(n)).isoformat() for n in range(cfg["lookback_days"] + 1)]
    for d in dates:
        if not args.date and not args.inspect and read_json(data / d / "meta.json", {"sources": {}})["sources"].get(sid, {}).get("status") == "ok":
            continue
        polys, labels, skipped, n_feat = collections.defaultdict(list), collections.defaultdict(set), collections.Counter(), collections.Counter()
        seen = collections.Counter()
        try:
            for layer in cfg["layers"]:
                url = cfg["endpoint"].format(date=d, layer=urllib.parse.quote(layer))
                z = zipfile.ZipFile(io.BytesIO(fetch(url)))
                kml = z.read(next(n for n in z.namelist() if n.lower().endswith(".kml")))
                for name, colour, plist, other in kml_shapes(kml):
                    for t in other:
                        skipped[t] += 1
                    if not plist:
                        continue
                    key = f"{layer}|{colour}"
                    cat = classify(key, {}, cfg["rules"])
                    label = re.sub(r"[\s\d/.:-]+$", "", name) or name   # drop trailing dates like "9/22"
                    polys[cat].extend(plist)
                    labels[cat].add(label)
                    n_feat[cat] += 1
                    seen[(key, label, cat)] += 1
        except Exception as e:
            if getattr(e, "code", None) == 404:
                continue   # not published for this date (yet)
            raise SourceError(f"could not read {url}: {e}")
        if args.inspect:
            print(f"Date {d}. Each distinct type (layer|colour | name): count -> category")
            for (key, label, cat), n in sorted(seen.items()):
                print(f"  {key} | {label}: {n} -> {cat}")
            return print("Ignored non-polygon items:", dict(skipped))
        save_polygons(sid, cfg, args, d, now, data, polys, labels, n_feat, {
            "snapshot_time": d, "endpoint": cfg["endpoint"], "skipped_non_polygon": dict(skipped)})
    print(f"[{sid}] checked {dates[-1]} to {dates[0]}")


def put_in_place(args, data, day, sid, filename, features):
    """Write to a working folder first, and only move the finished file into data/ once it is complete.
    If anything before this raises an exception, nothing here runs, so a half-built file never reaches data/
    and a day already saved from an earlier successful run is left untouched."""
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
    return final_path


def run_geoconfirmed(sid, cfg, args, day, now, data):
    """GeoConfirmed's geolocated events, saved as map points in each event's own date folder.
    Fields are copied as GeoConfirmed gives them (category = GeoConfirmed's icon name). Events with no date
    (permanent sites such as power plants) are counted in meta.json but not saved to any day."""
    end = dt.date.fromisoformat(day)
    start = end if args.date else end - dt.timedelta(cfg["lookback_days"])
    csv_url = cfg["csv"].format(conflict=cfg["conflict"], start=start, end=end)
    try:
        rows = list(csv.DictReader(io.StringIO(fetch(csv_url).decode("utf-8-sig")), delimiter=";"))
        gj = json.loads(fetch(cfg["geojson"].format(conflict=cfg["conflict"]), "application/json"))
        icons = json.loads(fetch(cfg["icons"].format(conflict=cfg["conflict"]), "application/json"))
    except Exception as e:
        raise SourceError(f"could not get data from GeoConfirmed: {e}")
    gj = json.loads(gj["geojson"]) if isinstance(gj.get("geojson"), str) else gj.get("geojson", gj)
    icon_of = {f["properties"]["id"]: f["properties"].get("icon") for f in gj["features"]}
    icon_name = {i["icon"]: i["name"] for f in icons for i in f["icons"]}
    side_color = {f["name"]: f["color"] for f in icons}
    links = lambda t: re.findall(r"https?://[^\s,]+", t or "")
    by_day, undated, no_category = collections.defaultdict(list), 0, 0
    for r in rows:
        d = (r.get("Date") or "")[:10]
        if not d:
            undated += 1
            continue
        icon = icon_of.get(r["Id"])
        cat = icon_name.get(icon)
        if not cat:
            no_category += 1
            cat = f"(category not found: {icon})"
        by_day[d].append({"type": "Feature",
            "geometry": {"type": "Point", "coordinates": [round(float(r["Longitude"]), 6), round(float(r["Latitude"]), 6)]},
            "properties": {"source": sid, "source_name": cfg["name"], "source_url": cfg["url"], "id": r["Id"], "date": d,
                "link": cfg["placemark_link"].format(id=r["Id"]), "category": cat, "side": r["Faction"],
                "color": side_color.get(r["Faction"], "#666666"), "description": r["Description"].strip(),
                "orbat": [u.strip() for u in (r["OrbatUnits"] or r["Units"]).split("|") if u.strip()],
                "geolocation": links(r["Geolocation"]), "sources": links(r["Source"])}})
    if args.inspect:
        print(f"{len(rows)} rows from {start} to {end}: {undated} undated; per day:", {d: len(v) for d, v in sorted(by_day.items())})
        print("Categories:", collections.Counter(f["properties"]["category"][:60] for v in by_day.values() for f in v).most_common())
        return
    filename = KIND_FILENAMES[cfg["kind"]]
    for d, features in sorted(by_day.items()):
        path = put_in_place(args, data, d, sid, filename, features)
        save_meta(data, d, sid, {"status": "ok", "fetched_at_utc": now.isoformat(timespec="seconds"), "endpoint": csv_url,
            "files": [f"{sid}/{filename}"], "events": len(features),
            "by_side": dict(collections.Counter(f["properties"]["side"] for f in features)), "category_not_found": sum(
                1 for f in features if f["properties"]["category"].startswith("(category not found"))})
        print(f"[{sid}] saved {path}  ({len(features)} events)")
    print(f"[{sid}] checked {start} to {end}; skipped {undated} undated placemarks; {no_category} events had no category match")


def save_polygons(sid, cfg, args, day, now, data, polys, labels, n_feat, extra):
    """Merge each category's polygons, save data/<day>/<source>/polygons/occupation.geojson, log it in meta.json."""
    hidden = set(cfg.get("leave_off_map", []))
    left_off = {c: sorted(labels[c]) for c in polys if c in hidden}
    polys = {c: p for c, p in polys.items() if c not in hidden}
    if not polys:
        raise SourceError(f"{day}: no polygons left to show; nothing saved (existing data left untouched).")
    features, by_cat, note = [], {}, ""
    for cat, plist in polys.items():
        geom, note = dissolve(plist, cfg["simplify_degrees"], cfg.get("cleanup_buffer_degrees", 0))
        area = polygons_area_km2(geom["coordinates"] if geom["type"] == "MultiPolygon" else [geom["coordinates"]])
        by_cat[cat] = {"source_polygons": n_feat[cat], "area_km2_approx": round(area)}
        features.append({"type": "Feature", "geometry": geom, "properties": {
            "source": sid, "source_name": cfg["name"], "source_url": cfg["url"],
            "category": cat, "category_label": CATEGORIES.get(cat, {}).get("label", cat),
            "snapshot_time": extra["snapshot_time"], "fetched_at_utc": now.isoformat(timespec="seconds"),
            "source_labels": sorted(labels[cat]), "source_polygons": n_feat[cat],
            "area_km2_approx": round(area), "processing": note}})

    filename = KIND_FILENAMES[cfg["kind"]]
    final_path = put_in_place(args, data, day, sid, filename, features)
    entry = {"status": "ok", "fetched_at_utc": now.isoformat(timespec="seconds"), **extra,
             "files": [f"{sid}/{filename}"], "by_category": by_cat, "unmapped_labels": sorted(labels.get("unmapped", [])),
             "processing": note}
    if left_off:
        entry["left_off_map"] = left_off
    save_meta(data, day, sid, entry)

    print(f"[{sid}] saved {final_path}  ({note})")
    for cat, v in by_cat.items():
        print(f"  {cat}: {v['source_polygons']} source polygons, about {v['area_km2_approx']:,} km2")
    if left_off:
        print("  Left off the map:", left_off)
    if "unmapped" in by_cat:
        print("  WARNING: some types matched no rule:", "; ".join(sorted(labels["unmapped"])))
    if extra.get("skipped_non_polygon"):
        print("  Ignored non-polygon items:", extra["skipped_non_polygon"])


KINDS = {"occupation": run_occupation, "kmz_layers": run_kmz_layers, "geoconfirmed": run_geoconfirmed}   # add new kinds of source here
# Output file for each kind, saved as data/<day>/<source>/<data type>/<specific data>.geojson.
# meta.json lists each source's files, and the dashboard reads them from there.
KIND_FILENAMES = {"occupation": "polygons/occupation.geojson", "kmz_layers": "polygons/occupation.geojson",
                  "geoconfirmed": "points/events.geojson"}


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

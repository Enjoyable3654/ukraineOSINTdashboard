#!/usr/bin/env python3
"""
ALL daily data updates live in this one file.

  python update.py                        run every enabled source, save into data/<today>/
  python update.py --only deepstate       run just one source
  python update.py --inspect deepstate    print what one source returns; saves nothing

HOW TO ADD A SOURCE: copy the "deepstate" block in SOURCES below, give it a new name, and change its address and
rules. Sources that return map polygons ("kind": "occupation" for GeoJSON, "kmz_layers" for dated KMZ files)
need nothing else. "geoconfirmed", "warspotting" and "telegram_channel" save geolocated events as map points;
"war_fires" saves The Economist's war-fire model detections as map points; "telegram_posts" saves a channel's
text posts for the Posts tab (give it a "group" from POST_GROUPS). Other kinds (points, posts) get their own function in the CODE section and an entry in KINDS.

Acquired data is never altered: every original feature, field and text is kept exactly as received (map shapes are
not merged, simplified or rounded); area sources also archive their original downloads byte for byte. Big files are
stored gzip-compressed (lossless). Anything we work out (categories, change layers, statistics, summaries) is added
alongside, as derived data. Polygons that match no rule are kept as "unmapped". One failing source never stops the
others, and a failed run never overwrites good data.
"""
import argparse, collections, csv, datetime as dt, gzip, html, io, json, math, os, re, shutil, sys, time, urllib.parse, urllib.request, zipfile
import xml.etree.ElementTree as ET
from pathlib import Path

try:
    from shapely.geometry import shape, mapping
    from shapely.ops import unary_union
    from shapely import force_2d, make_valid
    from shapely.strtree import STRtree
    HAVE_SHAPELY = True
except ImportError:  # still runs, but polygons are not merged or simplified
    HAVE_SHAPELY = False

ROOT = Path(__file__).resolve().parent
REF = ROOT / "ref"   # OCHA boundary files, unchanged and gzipped (see build_reference); credit: OCHA / SSPE "Kartographia", CC BY 3.0 IGO

# =====================================================================================================
# SETTINGS (edit this part)
# =====================================================================================================

USER_AGENT = "ukraine-osint-dashboard/1.0 (+https://github.com/Enjoyable3654/ukraineOSINTdashboard)"

CATEGORIES = {   # shared by all sources; "color_dark"/"outline" are used by the map in dark mode / as borders
    "ukraine":   {"label": "Ukraine-controlled / recently liberated", "color": "#2a7de1", "color_dark": "#5aa9ff"},
    "russia":    {"label": "Russian-occupied", "color": "#d64545", "color_dark": "#ff6b6b"},
    "contested": {"label": "Contested / unknown status", "color": "#444444", "color_dark": "#a0a0a0"},
    "claims":    {"label": "Claimed by a party (unverified)", "color": "#8e5bd0", "color_dark": "#b58cf0"},
    "other":     {"label": "Other", "color": "#7f8c8d", "color_dark": "#b0bec5"},
    "unmapped":  {"label": "Unmapped source type (needs a rule)", "color": "#444444", "color_dark": "#a0a0a0"},
    # change layers
    "gained":    {"label": "Russian advance: became occupied", "color": "#7a0000", "color_dark": "#ff3b3b"},
    "lost":      {"label": "Ukrainian advance: became Ukrainian-held", "color": "#123f8c", "color_dark": "#5aa9ff"},
    "occupied_to_contested": {"label": "Occupied became contested", "color": "#444444", "color_dark": "#a0a0a0",
                              "outline": "#123f8c", "outline_dark": "#5aa9ff"},
    "ukrainian_to_contested": {"label": "Ukrainian-held became contested", "color": "#444444", "color_dark": "#a0a0a0",
                               "outline": "#7a0000", "outline_dark": "#ff3b3b"},
}

# Change layers: each area source's Russian-occupied area compared with this many days earlier.
CHANGE_PERIODS = {"1d": 1, "7d": 7, "30d": 30}
CHANGE_MIN_WIDTH_DEGREES = 0.0003   # about 30 m: thinner slivers in the derived change layers are line redrawing, not real change

POST_GROUPS = {   # the Posts tab's filter groups; each Posts source names one in its "group"
    "official_ua": "Official Ukrainian",
    "official_ru": "Official Russian",
    "unofficial_ua": "Unofficial Ukrainian (milbloggers etc.)",
    "unofficial_ru": "Unofficial Russian (milbloggers etc.)",
}

SOURCES = {
    "deepstate": {
        "enabled": True,
        "kind": "occupation",
        "name": "DeepStateMap",
        "url": "https://deepstatemap.live/en",
        "endpoint": "https://deepstatemap.live/api/history/last",   # latest map; used by --inspect and --from-file
        # Every past map version (its "id" is its publish time) and each version's shapes. Each day gets the last
        # version published by the end of that day (UTC). DeepState revises maps afterwards, so each run re-fetches
        # the last "lookback_days" days.
        "history": "https://deepstatemap.live/api/history/public",
        "snapshot": "https://deepstatemap.live/api/history/{id}/geojson",
        "lookback_days": 30,
        "name_separator": "///",      # DeepState names look like "<Ukrainian> /// <English> /// <stable code>"
        "name_part": 1,               # keep the English part (for display: popups, source_labels)
        "classify_part": 2,           # match rules against the stable code instead (does not change with wording)
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
        "leave_off_map": ["ukraine"],   # user's decision (2026-10-03); still listed by name in meta.json
    },
    "ukrdaily": {
        "enabled": True,
        "kind": "kmz_layers",
        "name": "UkrDailyUpdate",
        "url": "https://map.ukrdailyupdate.com/",
        # One KMZ file per layer per date. Files appear days after their date and may be revised, so each run
        # re-fetches the last "lookback_days" days, each under that date's own folder.
        "endpoint": "https://map.ukrdailyupdate.com/kmz/{date}/{layer}.kmz",
        "layers": ["Ukrainian", "Russians", "Contested Areas"],
        "lookback_days": 30,
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
        "leave_off_map": ["background", "ukraine"],
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
    "warspotting": {
        "enabled": True,
        "kind": "warspotting",
        "name": "WarSpotting",
        "url": "https://ukr.warspotting.net/",
        # Official API (https://ukr.warspotting.net/api/docs/). Reuse allowed for non-profit use and news with credit
        # (a link). Max 10 requests per 10 s, so requests are spaced out. Only Russian losses are covered.
        "day": "https://ukr.warspotting.net/api/losses/russia/{date}/{page}/",
        "recently_added": "https://ukr.warspotting.net/api/losses/russia/",
        "loss_link": "https://ukr.warspotting.net/view/{id}/",
        # Losses are filed under the date they were lost but often added weeks later. Each run re-reads the last
        # "lookback_days" days in full, plus the 100 most recently added (any date), merged by ID.
        "lookback_days": 7,
        "color": "#E00000",
    },
    "lost_warinua": {
        "enabled": True,
        "kind": "telegram_channel",
        "name": "lost_warinua (Telegram)",
        "url": "https://t.me/s/lost_warinua",
        "channel": "lost_warinua",
        # Read from the channel's public web preview (no login), newest page first, pausing between pages.
        # Each run re-reads posts published in the last "lookback_days" days; posts are merged by post number.
        "lookback_days": 3,
        "max_pages": 30,
        "category": "Telegram post",
        # Side as the post's text states it (first match wins); otherwise "Side not stated" in grey.
        "side_rules": [{"regex": "ВСУ", "side": "Claimed loss: Ukraine (ВСУ)", "color": "#0051CA"},
                       {"regex": "российск", "side": "Claimed loss: Russia", "color": "#E00000"}],
    },
    "economist_fires": {
        "enabled": True,
        "kind": "war_fires",
        "name": "The Economist war-fire model",
        "url": "https://github.com/TheEconomist/the-economist-war-fire-model",
        # MIT-licensed. One file with every fire classified as war-related since Feb 2022 (~8 MB compressed),
        # updated about twice a day. The model confirms fires only after watching later days, so recent days
        # change: each run re-saves the last "lookback_days" days in full.
        "csv": "https://raw.githubusercontent.com/TheEconomist/the-economist-war-fire-model/master/output-data/ukraine_war_fires.csv",
        "link": "https://www.economist.com/interactive/graphic-detail/ukraine-fires",
        "lookback_days": 14,
        "color": "#FF8C00",
    },
    # Posts tab: Telegram channels copied daily (text in original language; photos/videos only linked).
    # To add one, copy this block, rename it, and change "name", "url", "channel" and "group".
    "ua_mod": {
        "enabled": True,
        "kind": "telegram_posts",
        "name": "Ministry of Defence of Ukraine",
        "url": "https://t.me/s/ministry_of_defense_ua",
        "channel": "ministry_of_defense_ua",
        "group": "official_ua",
        "lookback_days": 2,
        "max_pages": 40,
    },
    "ru_mod": {
        "enabled": True,
        "kind": "telegram_posts",
        "name": "Ministry of Defence of Russia",
        "url": "https://t.me/s/mod_russia",
        "channel": "mod_russia",
        "group": "official_ru",
        "lookback_days": 2,
        "max_pages": 40,
    },
    # "another_source": { ...copy a block above and change it... },
    # Place and region statistics (derived): runs after all sources and before the summary. Uses OCHA's boundaries
    # in ref/ (raions and settlement outlines). For each day of the window: (a) settlements inside each change patch,
    # per area source and comparison period; (b) events, fires and changed area per oblast and raion; (c) where the
    # area sources agree on changes. Saved as data/<day>/place_stats/stats/facts.json.
    "place_stats": {
        "enabled": True,
        "kind": "geo_analysis",
        "name": "Place and region statistics",
        "url": "https://data.humdata.org/dataset/cod-ab-ukr",
        "lookback_days": 30,
        "area_sources": ["deepstate", "ukrdaily"],
    },
    # Daily summary: runs last, reads everything saved for the previous day and asks Gemini (Google, free tier) to
    # summarise it. No fallback by the user's choice (2026-10-04): if it fails, the error is saved and shown instead.
    # The API key comes from the GEMINI_API_KEY secret; it is never written to any file.
    "daily_summary": {
        "enabled": True,
        "kind": "llm_summary",
        "name": "Daily summary (Gemini)",
        "url": "https://ai.google.dev/gemini-api",
        "model": "gemini-3.8-flash",   # gemini-2.5-flash is closed to new users (Google, 2026-10)
        "endpoint": "https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent",
        # Usage limits: one request per day; input capped at this many characters; output capped.
        "max_input_chars": 300000,
        "generation": {"maxOutputTokens": 4000},
        "instructions": (
            "You are summarising one day of open-source reporting on the Russia-Ukraine war for a public dashboard. "
            "Write in English, about 300-500 words, in short sections: Front line, Strikes and losses, Official statements. "
            "Rules: attribute every claim to its source and say which side it comes from; when sources disagree, give each "
            "version separately and never merge them into one 'truth'; say when something is unverified or only claimed; "
            "use only the material below, add nothing from memory; do not name private individuals; translate quoted "
            "Ukrainian or Russian into English. If the material is thin, say so briefly instead of padding."),
    },
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
    if not path.exists():
        return default
    return json.loads(gzip.decompress(path.read_bytes()) if path.suffix == ".gz" else path.read_text("utf-8"))


def write_bytes(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    for i in range(5):   # on Windows, antivirus or file sync can briefly lock a file that was just written
        try:
            return path.write_bytes(content)
        except OSError:
            if i == 4:
                raise
            time.sleep(0.5)


def gz(content):
    """Lossless gzip with a fixed timestamp, so identical content always gives identical bytes (no repo growth)."""
    return gzip.compress(content, compresslevel=9, mtime=0)


def write_json(path, obj):
    text = json.dumps(obj, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    write_bytes(path, gz(text) if path.suffix == ".gz" else text)


def run_occupation(sid, cfg, args, day, now, data):
    """DeepState-style source: for each day of the look-back window, the last map version published by the end of
    that day (UTC) is archived unchanged and its polygons saved as received (with a category added); then the
    change layers are rebuilt."""
    if args.inspect or args.from_file:
        try:
            raw = open(args.from_file, "rb").read() if args.from_file else fetch(cfg["endpoint"], "application/json")
        except Exception as e:
            raise SourceError(f"could not get data from {args.from_file or cfg['endpoint']}: {e}")
        payload = json.loads(raw)
        snap = payload.get("datetime") if isinstance(payload, dict) else None
        return occupation_from_payload(sid, cfg, args, day, now, data, raw, snap, args.from_file or cfg["endpoint"])
    try:
        versions = sorted(int(v["id"]) for v in json.loads(fetch(cfg["history"], "application/json")))
    except Exception as e:
        raise SourceError(f"could not get the list of map versions from {cfg['history']}: {e}")
    end, days, last, raw = dt.date.fromisoformat(day), [], None, None
    for n in range(0 if args.date else cfg["lookback_days"], -1, -1):
        d = end - dt.timedelta(n)
        cutoff = dt.datetime.combine(d + dt.timedelta(1), dt.time(), dt.timezone.utc).timestamp()
        vid = max((v for v in versions if v < cutoff), default=None)
        if vid is None:
            continue
        url = cfg["snapshot"].format(id=vid)
        if vid != last:   # consecutive days often share a version: download it once
            time.sleep(1)
            try:
                raw, last = fetch(url, "application/json"), vid
            except Exception as e:
                raise SourceError(f"could not get {url}: {e}")
        snap = dt.datetime.fromtimestamp(vid, dt.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
        occupation_from_payload(sid, cfg, args, d.isoformat(), now, data, raw, snap, url)
        days.append(d.isoformat())
    compute_changes(sid, cfg, args, data, days)


def occupation_from_payload(sid, cfg, args, day, now, data, raw, snap, endpoint):
    """Archive one map version unchanged and save its polygons, as received, for one day."""
    payload = json.loads(raw)
    fc = find_feature_collection(payload)
    if not fc:
        raise SourceError("no GeoJSON FeatureCollection found in the response. Run --inspect and send the output to Claude.")
    if args.inspect:
        return print_inspect(payload, fc, cfg)
    feats, skipped = [], collections.Counter()
    for f in fc["features"]:
        g, props = f.get("geometry") or {}, f.get("properties") or {}
        if g.get("type") not in ("Polygon", "MultiPolygon"):
            skipped[str(g.get("type"))] += 1   # kept in the archived original
            continue
        feats.append((f, label_of(props, cfg), classify(classify_key(props, cfg), props, cfg["rules"])))
    if not feats:
        raise SourceError("the response contained no polygons; nothing saved (existing data left untouched).")
    put_in_place(args, data, day, sid, "raw/snapshot.json.gz", content=gz(raw))
    save_areas(sid, cfg, args, day, now, data, feats, {"snapshot_time": snap, "endpoint": endpoint,
                                                       "skipped_non_polygon": dict(skipped), "original": f"{sid}/raw/snapshot.json.gz"})


def compute_changes(sid, cfg, args, data, days):
    """For each given day, how this source's map changed compared with 1, 7 and 30 days earlier. Each spot is
    Ukrainian-held (U), contested (C) or occupied (R). Drawn: "gained" = became occupied (U->R, C->R);
    "lost" = became Ukrainian-held (R->U, C->U), merged where touching; "occupied_to_contested" (R->C) and
    "ukrainian_to_contested" (U->C). Saved as polygons/change_<period>.geojson; the area of each of the six
    transitions goes in meta.json under "change_stats" so the map can total them either way. Slivers thinner
    than CHANGE_MIN_WIDTH_DEGREES are dropped (they come from daily simplification, not real change)."""
    if not HAVE_SHAPELY:
        return print(f"[{sid}] change layers skipped: shapely is not installed")
    fn, eps, cache = KIND_FILENAMES[cfg["kind"]], CHANGE_MIN_WIDTH_DEGREES, {}
    empty = shape({"type": "Polygon", "coordinates": []})

    def areas(d):   # (occupied, contested) shapes of day d, or None if the day has no saved map
        if d not in cache:
            f, g = read_json(data / d / sid / fn, None), collections.defaultdict(list)
            for x in (f or {"features": []})["features"]:
                g[x["properties"]["category"]].append(force_2d(shape(x["geometry"])).buffer(0))
            cache[d] = (unary_union(g["russia"]), unary_union(g["contested"]) if g["contested"] else empty) if g["russia"] else None
        return cache[d]

    clean = lambda g: g.buffer(-eps, join_style="mitre").buffer(eps, join_style="mitre")
    km2 = lambda g: 0 if g.is_empty else round(polygons_area_km2((lambda m: m["coordinates"] if m["type"] == "MultiPolygon"
                                                                   else [m["coordinates"]])(mapping(g))), 1)
    for d in days:
        meta = read_json(data / d / "meta.json", {"sources": {}})["sources"].get(sid)
        if not meta or areas(d) is None:
            continue
        meta["files"], meta["change_stats"] = [f for f in meta.get("files", []) if "/change_" not in f], {}
        rn, cn = areas(d)
        for period, n in CHANGE_PERIODS.items():
            then = (dt.date.fromisoformat(d) - dt.timedelta(n)).isoformat()
            if areas(then) is None:
                continue
            rt, ct = areas(then)
            hn, ht = rn.union(cn), rt.union(ct)   # held = occupied or contested
            t = {"u2r": clean(rn.difference(ht)), "c2r": clean(rn.intersection(ct)), "u2c": clean(cn.difference(ht)),
                 "r2c": clean(rt.intersection(cn)), "r2u": clean(rt.difference(hn)), "c2u": clean(ct.difference(hn))}
            shapes = {"gained": clean(rn.difference(rt)), "lost": clean(ht.difference(hn)),
                      "occupied_to_contested": t["r2c"], "ukrainian_to_contested": t["u2c"]}
            feats = []
            for cat, g in shapes.items():
                if g.is_empty:
                    continue
                m = mapping(g)
                feats.append({"type": "Feature", "geometry": {"type": m["type"], "coordinates": xy(m["coordinates"])}, "properties": {
                    "source": sid, "source_name": cfg["name"], "source_url": cfg["url"], "category": cat,
                    "category_label": CATEGORIES[cat]["label"], "period": period, "compared_with": then,
                    "snapshot_time": d, "area_km2_approx": km2(g)}})
            meta["change_stats"][period] = {"compared_with": then, "km2": {k: km2(g) for k, g in t.items()}}
            name = f"polygons/change_{period}.geojson"
            put_in_place(args, data, d, sid, name, feats)
            meta["files"].append(f"{sid}/{name}")
        save_meta(data, d, sid, meta)
    print(f"[{sid}] change layers rebuilt for {len(days)} days")


def kml_shapes(kml):
    """For each Placemark in a KML file: its fields as given (name, styleUrl, description), colour from its style,
    its polygons as a GeoJSON geometry with every coordinate value as written (or None), and non-polygon types."""
    num = lambda t: [[float(v) for v in p.split(",")] for p in t.split()]
    for pm in ET.fromstring(kml).iterfind(".//{*}Placemark"):
        style = pm.findtext("{*}styleUrl") or ""
        m = re.search(r"[0-9A-Fa-f]{6}", style)
        polys = [[num(r.text) for r in [pg.find("{*}outerBoundaryIs//{*}coordinates")] + pg.findall("{*}innerBoundaryIs//{*}coordinates")
                  if r is not None] for pg in pm.iterfind(".//{*}Polygon")]
        geom = None if not polys else {"type": "Polygon", "coordinates": polys[0]} if len(polys) == 1 else {"type": "MultiPolygon", "coordinates": polys}
        other = [t for t in ("Point", "LineString") if pm.find(".//{*}" + t) is not None]
        fields = {"name": (pm.findtext("{*}name") or ""), "styleUrl": style, "description": pm.findtext("{*}description")}
        yield fields, m.group(0).upper() if m else "", geom, other


def run_kmz_layers(sid, cfg, args, day, now, data):
    """A source that publishes one KMZ (zipped KML) file per layer per date. Each date of the look-back window is
    re-fetched and saved in its own day folder; then the change layers are rebuilt."""
    today = dt.date.fromisoformat(day)
    dates = [day] if args.date else [(today - dt.timedelta(n)).isoformat() for n in range(cfg["lookback_days"] + 1)]
    saved = []
    for d in dates:
        feats, skipped, seen, raws = [], collections.Counter(), collections.Counter(), {}
        try:
            for layer in cfg["layers"]:
                url = cfg["endpoint"].format(date=d, layer=urllib.parse.quote(layer))
                time.sleep(1)
                raws[layer] = fetch(url)
                z = zipfile.ZipFile(io.BytesIO(raws[layer]))
                kml = z.read(next(n for n in z.namelist() if n.lower().endswith(".kml")))
                for fields, colour, geom, other in kml_shapes(kml):
                    for t in other:
                        skipped[t] += 1
                    if not geom:
                        continue
                    key = f"{layer}|{colour}"
                    cat = classify(key, {}, cfg["rules"])
                    label = re.sub(r"[\s\d/.:-]+$", "", fields["name"].strip()) or fields["name"]   # without trailing dates like "9/22"
                    feats.append(({"type": "Feature", "geometry": geom, "properties": {**fields, "layer": layer}}, label, cat))
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
        for layer, content in raws.items():   # the original KMZ files, byte for byte
            put_in_place(args, data, d, sid, f"raw/{layer}.kmz", content=content)
        save_areas(sid, cfg, args, d, now, data, feats, {"snapshot_time": d, "endpoint": cfg["endpoint"],
            "skipped_non_polygon": dict(skipped), "original": [f"{sid}/raw/{layer}.kmz" for layer in raws]})
        saved.append(d)
    print(f"[{sid}] checked {dates[-1]} to {dates[0]}")
    compute_changes(sid, cfg, args, data, sorted(saved))


def put_in_place(args, data, day, sid, filename, features=None, content=None):
    """Write to a working folder first, and only move the finished file into data/ once it is complete.
    If anything before this raises an exception, nothing here runs, so a half-built file never reaches data/
    and a day already saved from an earlier successful run is left untouched. Saves `features` as a
    FeatureCollection (gzipped if the name ends in .gz), or `content` bytes exactly as given."""
    work_path = args.working_dir_path / day / sid / filename
    if content is None:
        write_json(work_path, {"type": "FeatureCollection", "features": features})
    else:
        write_bytes(work_path, content)
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
            "geometry": {"type": "Point", "coordinates": [float(r["Longitude"]), float(r["Latitude"])]},
            "properties": {"original": {**r, "icon": icon}, "source": sid, "source_name": cfg["name"], "source_url": cfg["url"], "id": r["Id"], "date": d,
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


def run_warspotting(sid, cfg, args, day, now, data):
    """WarSpotting's documented equipment losses, saved as map points in each loss's own date folder.
    Losses with no coordinates are left off the map; their IDs are listed in meta.json. Every loss is keyed
    by its WarSpotting ID, so one fetched twice, or already saved, is never duplicated."""
    end = dt.date.fromisoformat(day)
    full_days = [(end - dt.timedelta(n)).isoformat() for n in range(0 if args.date else cfg["lookback_days"], -1, -1)]
    get = lambda url: (time.sleep(1.1), json.loads(fetch(url, "application/json"))["losses"])[1]   # stays under 10 per 10 s
    losses = {}
    try:
        for d in full_days:
            page = 1
            while True:
                batch = get(cfg["day"].format(date=d, page=page))
                losses.update({x["id"]: x for x in batch})
                if len(batch) < 100:
                    break
                page += 1
        if not args.date:
            losses.update({x["id"]: x for x in get(cfg["recently_added"])})
    except Exception as e:
        raise SourceError(f"could not get data from WarSpotting: {e}")
    by_day = collections.defaultdict(dict)
    for x in losses.values():
        by_day[x["date"]][x["id"]] = x
    if args.inspect:
        print({d: len(v) for d, v in sorted(by_day.items())})
        return print("Without coordinates:", sum(1 for x in losses.values() if not x.get("geo")), "of", len(losses))
    found = collections.defaultdict(dict)
    for d, day_losses in by_day.items():
        for i, x in day_losses.items():
            if not x.get("geo"):
                found[d][i] = None
                continue
            lat, lon = (float(v) for v in x["geo"].split(","))
            found[d][i] = {"type": "Feature", "geometry": {"type": "Point", "coordinates": [lon, lat]},
                "properties": {"original": x, "source": sid, "source_name": cfg["name"], "source_url": cfg["url"], "id": i, "date": d,
                    "link": cfg["loss_link"].format(id=i), "category": x.get("type") or "", "side": f"Lost by {x.get('lost_by')}",
                    "color": cfg["color"], "description": " · ".join(v for v in [x.get("model"), x.get("status"),
                        x.get("nearest_location") and f"near {x['nearest_location']}", x.get("tags") and f"tags: {x['tags']}"] if v),
                    "orbat": [x["unit"]] if x.get("unit") else []}}
    save_points_merged(sid, cfg, args, data, now, found, set(full_days), cfg["day"].format(date="<date>", page=1))


def save_points_merged(sid, cfg, args, data, now, found, replace_days, endpoint):
    """found = {date: {id: map point, or None if it has no coordinates}}. Days in replace_days were re-read in
    full and replace what was saved; any other day is merged into what is already saved, matched by ID, so an
    item fetched twice or already saved is never duplicated. Items without coordinates are left off the map;
    their IDs are listed in meta.json."""
    filename = KIND_FILENAMES[cfg["kind"]]
    for d in sorted(set(found) | set(replace_days)):
        old_meta = read_json(data / d / "meta.json", {"sources": {}})["sources"].get(sid, {})
        if d in replace_days:
            features, no_geo = {}, set()
        else:
            saved = read_json(data / d / sid / filename, {"features": []})["features"]
            features, no_geo = {f["properties"]["id"]: f for f in saved}, set(old_meta.get("no_coordinates_ids", []))
        for i, f in found.get(d, {}).items():
            if f is None:
                no_geo.add(i)
                features.pop(i, None)
            else:
                features[i] = f
                no_geo.discard(i)
        if not features and not no_geo:
            continue
        entry = {"status": "ok", "fetched_at_utc": now.isoformat(timespec="seconds"), "endpoint": endpoint,
                 "events": len(features), "no_coordinates": len(no_geo), "no_coordinates_ids": sorted(no_geo)}
        if features:
            put_in_place(args, data, d, sid, filename, list(features.values()))
            entry["files"] = [f"{sid}/{filename}"]
        save_meta(data, d, sid, entry)
        print(f"[{sid}] {d}: {len(features)} saved, {len(no_geo)} without coordinates (left off the map)")


def run_war_fires(sid, cfg, args, day, now, data):
    """Satellite fire detections that The Economist's model classifies as war-related, as map points per day.
    Days in the look-back window are replaced in full each run, since the model revises recent days."""
    end = dt.date.fromisoformat(day)
    days = {(end - dt.timedelta(n)).isoformat() for n in range(0 if args.date else cfg["lookback_days"], -1, -1)}
    try:
        rows = csv.DictReader(io.StringIO(fetch(cfg["csv"]).decode("utf-8")))
        by_day = collections.defaultdict(list)
        for r in rows:
            if r["date"] in days:
                t = r["ACQ_TIME"].zfill(4)
                by_day[r["date"]].append({"type": "Feature",
                    "geometry": {"type": "Point", "coordinates": [float(r["LONGITUDE"]), float(r["LATITUDE"])]},
                    "properties": {"original": r, "source": sid, "source_name": cfg["name"], "source_url": cfg["url"], "id": len(by_day[r["date"]]),
                        "date": r["date"], "link": cfg["link"], "category": "Fire classified as war-related (model estimate)",
                        "side": "Not attributed", "color": cfg["color"], "radius": 3, "orbat": [],
                        "description": f"Satellite heat detection at {t[:2]}:{t[2:]} UTC"
                            + (", in an area of abnormal fire activity." if r["war_fire_restrictive"] == "1"
                               else ", in an area days after abnormal fire activity.")
                            + (" Urban area." if r["in_urban_area"] == "TRUE" else "")}})
    except Exception as e:
        raise SourceError(f"could not read {cfg['csv']}: {e}")
    if args.inspect:
        return print({d: len(by_day.get(d, [])) for d in sorted(days)})
    filename = KIND_FILENAMES[cfg["kind"]]
    for d in sorted(days):
        f = by_day.get(d, [])
        entry = {"status": "ok", "fetched_at_utc": now.isoformat(timespec="seconds"), "endpoint": cfg["csv"], "events": len(f)}
        if f:
            put_in_place(args, data, d, sid, filename, f)
            entry["files"] = [f"{sid}/{filename}"]
        save_meta(data, d, sid, entry)
        print(f"[{sid}] {d}: {len(f)} fires")


COORDS = r"(-?\d{1,2}\.\d{2,})\s*,\s*(-?\d{1,3}\.\d{2,})"


def telegram_posts(page, channel):
    """(post number, publish time, message HTML) for each post on a t.me/s/<channel> page."""
    for b in re.split(r'(?=<div class="tgme_widget_message_wrap)', page)[1:]:
        m = re.search(rf'data-post="{channel}/(\d+)"', b)
        t = re.search(r'<time datetime="([^"]+)"', b)
        x = re.search(r'<div class="tgme_widget_message_text[^"]*"[^>]*>(.*?)</div>', b, re.S)
        if m and t and x:
            yield int(m.group(1)), dt.datetime.fromisoformat(t.group(1)), x.group(1)


def telegram_recent(cfg, cutoff):
    """Posts from a channel's public web preview published after cutoff: newest page first, 2 s between pages."""
    url = cfg["url"]
    for _ in range(cfg["max_pages"]):
        posts = list(telegram_posts(fetch(url, "text/html").decode("utf-8"), cfg["channel"]))
        time.sleep(2)
        yield from (p for p in posts if p[1] >= cutoff)
        if not posts or min(w for _, w, _ in posts) < cutoff:
            return
        url = f"{cfg['url']}?before={min(p for p, _, _ in posts)}"


def telegram_lines_links(body):
    """A post's non-empty text lines, and every link in it (hyperlinked words and plain links), in order."""
    links = list(dict.fromkeys(h for h in (html.unescape(html.unescape(x)) for x in re.findall(r'href="([^"]+)"', body)) if h.startswith("http")))
    lines = [l for l in (html.unescape(re.sub(r"<[^>]+>", "", x)).strip() for x in re.split(r"<br\s*/?>", body)) if l]
    return lines, links


def run_telegram_posts(sid, cfg, args, day, now, data):
    """A public Telegram channel's text posts for the Posts tab, filed under the day they were posted (UTC).
    Merged by post number, so a post read on two runs is saved once."""
    cutoff, found, n = now - dt.timedelta(days=cfg["lookback_days"]), collections.defaultdict(dict), 0
    try:
        for pid, when, body in telegram_recent(cfg, cutoff):
            lines, links = telegram_lines_links(body)
            n += 1
            found[when.date().isoformat()][pid] = {"type": "Feature", "geometry": None, "properties": {
                "source": sid, "source_name": cfg["name"], "group": cfg["group"], "id": pid, "posted_utc": when.isoformat(),
                "link": f"https://t.me/{cfg['channel']}/{pid}", "text": "\n".join(lines), "links": links, "original_html": body}}
    except Exception as e:
        raise SourceError(f"could not read {cfg['url']}: {e}")
    if args.inspect:
        return print(f"{n} posts since {cutoff:%Y-%m-%d %H:%M}:", {d: len(v) for d, v in sorted(found.items())})
    save_points_merged(sid, cfg, args, data, now, found, set(), cfg["url"])


def run_telegram(sid, cfg, args, day, now, data):
    """A public Telegram channel's posts, as map points filed under the date written on the post's first line
    (or the day it was posted, if there is none). Takes the coordinates, the text in its original language,
    every link in the post (hyperlinked words such as "Источник" and plain links), and a link to the post."""
    ch, cutoff = cfg["channel"], now - dt.timedelta(days=cfg["lookback_days"])
    found, n_posts, no_date = collections.defaultdict(dict), 0, 0
    try:
        for pid, when, body in telegram_recent(cfg, cutoff):
            n_posts += 1
            lines, links = telegram_lines_links(body)
            m = lines and re.fullmatch(r"(\d{2})\.(\d{2})\.(\d{4}|\d{2})", lines[0])   # 20.09.2026 or 20.09.26
            try:
                d, note = dt.date(int(m.group(3)) % 100 + 2000, int(m.group(2)), int(m.group(1))).isoformat(), None
                lines = lines[1:]
            except (AttributeError, TypeError, ValueError):
                d, note = when.date().isoformat(), "no date in post; day it was posted"
                no_date += 1
            c = re.search(COORDS, " ".join(lines))
            text = "\n".join(l for l in lines if not re.fullmatch(COORDS, l.strip("() ")) and not l.startswith("http")
                             and not re.match(r"(Источник|Джерело|Source)\b", l, re.I))
            rule = next((r for r in cfg["side_rules"] if re.search(r["regex"], text)), {"side": "Side not stated", "color": "#666666"})
            found[d][pid] = c and {"type": "Feature",
                "geometry": {"type": "Point", "coordinates": [float(c.group(2)), float(c.group(1))]},
                "properties": {"source": sid, "source_name": cfg["name"], "source_url": cfg["url"], "id": pid, "date": d,
                    "date_note": note, "posted_utc": when.isoformat(), "link": f"https://t.me/{ch}/{pid}",
                    "category": cfg["category"], "side": rule["side"], "color": rule["color"], "description": text,
                    "orbat": [], "sources": links, "original_html": body}}
    except Exception as e:
        raise SourceError(f"could not read {cfg['url']}: {e}")
    if args.inspect:
        return print(f"{n_posts} posts since {cutoff:%Y-%m-%d %H:%M}; {no_date} without a date line;",
                     {d: f"{sum(1 for f in v.values() if f)} with / {sum(1 for f in v.values() if not f)} without coordinates" for d, v in sorted(found.items())})
    save_points_merged(sid, cfg, args, data, now, found, set(), cfg["url"])
    print(f"[{sid}] read {n_posts} posts published since {cutoff:%Y-%m-%d %H:%M} UTC; {no_date} had no date line")


def area_km2(g):
    """Area of a shapely shape in km2 (derived)."""
    if g.is_empty:
        return 0
    m = mapping(force_2d(g))
    polys = m["coordinates"] if m["type"] == "MultiPolygon" else [m["coordinates"]] if m["type"] == "Polygon" else \
        [p for x in m.get("geometries", []) if x["type"] in ("Polygon", "MultiPolygon") for p in (x["coordinates"] if x["type"] == "MultiPolygon" else [x["coordinates"]])]
    return round(polygons_area_km2(polys), 2)


def run_geo_analysis(sid, cfg, args, day, now, data):
    """Derived place/region facts for each day of the window (see the "place_stats" settings)."""
    if not HAVE_SHAPELY:
        raise SourceError("shapely is not installed")
    try:
        raions = read_json(REF / "ukr_admin2.geojson.gz", None)["features"]
        setts = read_json(REF / "ukr_admin4.geojson.gz", None)["features"]
    except Exception as e:
        raise SourceError(f"boundary files missing in ref/ (run --build-reference): {e}")
    fix = lambda g: make_valid(force_2d(shape(g))).buffer(0)   # repaired working copy in memory for the maths; files stay as received
    rg = [fix(f["geometry"]) for f in raions]
    sg = [fix(f["geometry"]) for f in setts]
    rtree, stree = STRtree(rg), STRtree(sg)
    rlab = [(f["properties"]["adm1_name"], f["properties"]["adm2_name"]) for f in raions]

    def region_of(pt):
        for i in rtree.query(pt):
            if rg[i].covers(pt):
                return rlab[i]
        return ("Outside Ukraine", "Outside Ukraine")

    def places(g):
        out = []
        for i in stree.query(g):
            inter = g.intersection(sg[i])
            if not inter.is_empty and inter.area >= 0.005 * sg[i].area:   # ignore touches under 0.5% of a settlement
                q = setts[i]["properties"]
                out.append({"name": q["adm4_name"], "name_uk": q["adm4_name1"], "type": q["adm4_type"], "hromada": q["adm3_name"],
                            "raion": q["adm2_name"], "oblast": q["adm1_name"], "share": round(inter.area / sg[i].area, 2)})
        return sorted(out, key=lambda x: -x["share"])

    end = dt.date.fromisoformat(day)
    for n in range(0 if args.date else cfg["lookback_days"], -1, -1):
        d = (end - dt.timedelta(n)).isoformat()
        meta = read_json(data / d / "meta.json", {"sources": {}})["sources"]
        if not meta:
            continue
        facts = {"date": d, "places": {}, "regions": {"points": {}, "changes": {}}, "agreement": {}}
        changes = {}   # changes[src][period][category] = shapely shape
        for src, m in meta.items():
            for f in [f for f in m.get("files", []) if re.search(r"\.geojson(\.gz)?$", f)] if m.get("status") == "ok" else []:
                hit = re.search(r"/change_(\w+)\.geojson", f)
                feats = read_json(data / d / f, {"features": []})["features"]
                if hit and src in cfg["area_sources"]:
                    for x in feats:
                        changes.setdefault(src, {}).setdefault(hit.group(1), {})[x["properties"]["category"]] = fix(x["geometry"])
                elif "/points/" in f:   # (b) points per oblast and raion
                    cnt = facts["regions"]["points"].setdefault(src, {})
                    for x in feats:
                        ob, ra = region_of(force_2d(shape(x["geometry"])))
                        cnt.setdefault(ob, {"total": 0, "raions": {}})
                        cnt[ob]["total"] += 1
                        cnt[ob]["raions"][ra] = cnt[ob]["raions"].get(ra, 0) + 1
        for src, per in changes.items():
            for period, cats in per.items():
                for cat, g in cats.items():
                    facts["places"].setdefault(src, {}).setdefault(period, {})[cat] = places(g)            # (a)
                    reg = facts["regions"]["changes"].setdefault(src, {}).setdefault(period, {}).setdefault(cat, {})
                    for i in rtree.query(g):                                                             # (b) km2 per raion
                        a = area_km2(g.intersection(rg[i]))
                        if a > 0:
                            reg[f"{rlab[i][1]}, {rlab[i][0]}"] = a
        a, b = cfg["area_sources"]
        for period in CHANGE_PERIODS:                                                                    # (c) agreement
            if period not in changes.get(a, {}) or period not in changes.get(b, {}):
                continue
            for cat in ("gained", "lost", "occupied_to_contested", "ukrainian_to_contested"):
                ga, gb = changes[a][period].get(cat), changes[b][period].get(cat)
                if ga is None and gb is None:
                    continue
                e = shape({"type": "Polygon", "coordinates": []})
                ga, gb = ga if ga is not None else e, gb if gb is not None else e
                both = ga.intersection(gb)
                facts["agreement"].setdefault(period, {})[cat] = {"both_km2": area_km2(both), f"{a}_only_km2": area_km2(ga.difference(gb)),
                    f"{b}_only_km2": area_km2(gb.difference(ga)), "places_both": [x["name"] for x in places(both)] if not both.is_empty else []}
        fn = KIND_FILENAMES[cfg["kind"]]
        put_in_place(args, data, d, sid, fn, content=json.dumps(facts, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
        save_meta(data, d, sid, {"status": "ok", "fetched_at_utc": now.isoformat(timespec="seconds"), "files": [f"{sid}/{fn}"],
                                 "boundaries": "OCHA COD-AB v05 (CC BY 3.0 IGO)"})
    print(f"[{sid}] place and region statistics saved for the last {cfg['lookback_days'] + 1} days")


def run_llm_summary(sid, cfg, args, day, now, data):
    """Summarise everything saved for one day (default: the day before, which is complete) with Gemini.
    Saves data/<day>/<source>/text/summary.json, or the error in meta.json if anything fails."""
    d = day if args.date else (dt.date.fromisoformat(day) - dt.timedelta(1)).isoformat()
    meta = read_json(data / d / "meta.json", {"sources": {}})["sources"]
    lines = []
    for src, m in meta.items():
        name = SOURCES.get(src, {}).get("name", src)
        for f in [f for f in m.get("files", []) if re.search(r"/(posts|points)/[^/]+\.geojson(\.gz)?$", f)] if m.get("status") == "ok" else []:
            for x in read_json(data / d / f, {"features": []})["features"]:
                p = x["properties"]
                if "/posts/" in f:
                    lines.append(f"[{name} | {POST_GROUPS.get(p['group'], p['group'])} | {p['posted_utc'][11:16]} UTC] {p['text']}")
                elif "/points/events" in f:
                    lines.append(f"[{name} | event | side: {p.get('side')}] {p.get('category')}: {p.get('description')}")
        if src.endswith("fires") and m.get("events") is not None:
            lines.append(f"[{name}] {m['events']} satellite fire detections classified as war-related (model estimate).")
        c = m.get("change_stats", {}).get("1d")
        if c and c.get("km2"):
            k = c["km2"]
            lines.append(f"[{name} | map change vs {c['compared_with']}, km2] newly occupied {k['u2r'] + k['c2r']} "
                         f"(from contested {k['c2r']}), newly contested {k['u2c']}, back to Ukrainian-held {k['r2u'] + k['c2u']}, "
                         f"occupied became contested {k['r2c']}")
    f = read_json(data / d / "place_stats/stats/facts.json", None)
    if f:
        name = lambda s: SOURCES.get(s, {}).get("name", s)
        what = {"gained": "newly occupied", "lost": "back to Ukrainian-held", "occupied_to_contested": "occupied became contested",
                "ukrainian_to_contested": "Ukrainian-held became contested"}
        for src, per in f["places"].items():
            for cat, pl in per.get("1d", {}).items():
                if pl:
                    lines.append(f"[{name(src)} | places in '{what.get(cat, cat)}' area vs previous day (share of settlement inside)] "
                                 + "; ".join(f"{x['name']} ({x['type']}, {x['raion']} raion, {x['oblast']}) {round(x['share'] * 100)}%" for x in pl[:25]))
        for src, obl in f["regions"]["points"].items():
            lines.append(f"[{name(src)} | items per oblast] " + "; ".join(f"{o}: {v['total']}" for o, v in sorted(obl.items(), key=lambda kv: -kv[1]["total"])))
        for cat, v in f["agreement"].get("1d", {}).items():
            lines.append(f"[Area sources agreement, '{what.get(cat, cat)}' vs previous day, km2] " + ", ".join(f"{k}: {x}" for k, x in v.items() if k != "places_both")
                         + (f"; settlements where both agree: {', '.join(v['places_both'][:25])}" if v["places_both"] else ""))
    material = "\n".join(lines)[:cfg["max_input_chars"]]
    try:
        key = os.environ.get("GEMINI_API_KEY")
        if not key:
            raise RuntimeError("no GEMINI_API_KEY secret is set")
        if not lines:
            raise RuntimeError(f"nothing saved for {d} to summarise")
        req = urllib.request.Request(cfg["endpoint"].format(model=cfg["model"]), method="POST",
            headers={"Content-Type": "application/json", "x-goog-api-key": key, "User-Agent": USER_AGENT},
            data=json.dumps({"contents": [{"parts": [{"text": f"{cfg['instructions']}\n\nMaterial for {d}:\n{material}"}]}],
                             "generationConfig": cfg["generation"]}).encode())
        with urllib.request.urlopen(req, timeout=300) as r:
            out = json.loads(r.read().decode("utf-8"))
        text = "".join(p.get("text", "") for p in out["candidates"][0]["content"]["parts"]).strip()
        if not text:
            raise RuntimeError(f"Gemini returned no text ({out['candidates'][0].get('finishReason')})")
    except Exception as e:
        msg = getattr(e, "read", None) and e.read().decode("utf-8", "replace")[:300] or str(e)
        save_meta(data, d, sid, {"status": "error", "error": f"Summary could not be generated: {msg}",
                                 "at_utc": now.isoformat(timespec="seconds")})
        raise SourceError(f"{d}: {msg}")
    fn = KIND_FILENAMES[cfg["kind"]]
    write_json(args.working_dir_path / d / sid / fn, {"date": d, "text": text, "model": cfg["model"],
                                                      "generated_utc": now.isoformat(timespec="seconds"), "input_items": len(lines)})
    (data / d / sid / fn).parent.mkdir(parents=True, exist_ok=True)
    shutil.move(str(args.working_dir_path / d / sid / fn), str(data / d / sid / fn))
    save_meta(data, d, sid, {"status": "ok", "fetched_at_utc": now.isoformat(timespec="seconds"), "model": cfg["model"],
                             "input_items": len(lines), "files": [f"{sid}/{fn}"]})
    print(f"[{sid}] {d}: summary saved ({len(lines)} items in, {len(text.split())} words out)")


def save_areas(sid, cfg, args, day, now, data, feats, extra):
    """Save each polygon exactly as received, with derived fields added (category, label, area), as
    data/<day>/<source>/polygons/occupation.geojson.gz, and log it in meta.json. Categories the user chose to leave
    off the map are not drawn (they stay in the archived original and are listed by name in meta.json)."""
    hidden, out, by_cat, labels = set(cfg.get("leave_off_map", [])), [], {}, collections.defaultdict(set)
    for f, label, cat in feats:
        labels[cat].add(label)
        if cat in hidden:
            continue
        g = f["geometry"]
        area = polygons_area_km2([[[c[:2] for c in r] for r in p] for p in (g["coordinates"] if g["type"] == "MultiPolygon" else [g["coordinates"]])])
        b = by_cat.setdefault(cat, {"source_polygons": 0, "area_km2_approx": 0})
        b["source_polygons"] += 1
        b["area_km2_approx"] += area
        out.append({**f, "properties": {**(f.get("properties") or {}), "source": sid, "source_name": cfg["name"],
            "source_url": cfg["url"], "category": cat, "category_label": CATEGORIES.get(cat, {}).get("label", cat),
            "label": label, "snapshot_time": extra["snapshot_time"], "area_km2_approx": round(area, 2)}})
    if not out:
        raise SourceError(f"{day}: no polygons left to show; nothing saved (existing data left untouched).")
    for b in by_cat.values():
        b["area_km2_approx"] = round(b["area_km2_approx"])
    filename = KIND_FILENAMES[cfg["kind"]]
    final_path = put_in_place(args, data, day, sid, filename, out)
    left_off = {c: sorted(labels[c]) for c in labels if c in hidden}
    entry = {"status": "ok", "fetched_at_utc": now.isoformat(timespec="seconds"), **extra, "files": [f"{sid}/{filename}"],
             "by_category": by_cat, "unmapped_labels": sorted(labels.get("unmapped", [])), "processing": "unaltered"}
    if left_off:
        entry["left_off_map"] = left_off
    save_meta(data, day, sid, entry)
    print(f"[{sid}] saved {final_path}: " + ", ".join(f"{c} {v['source_polygons']} shapes ~{v['area_km2_approx']:,} km2" for c, v in by_cat.items()))
    if "unmapped" in by_cat:
        print("  WARNING: some types matched no rule:", "; ".join(sorted(labels["unmapped"])))


KINDS = {"occupation": run_occupation, "kmz_layers": run_kmz_layers, "geoconfirmed": run_geoconfirmed,
         "warspotting": run_warspotting, "telegram_channel": run_telegram, "war_fires": run_war_fires,
         "telegram_posts": run_telegram_posts, "llm_summary": run_llm_summary,
         "geo_analysis": run_geo_analysis}   # add new kinds of source here
# Output file for each kind, saved as data/<day>/<source>/<data type>/<specific data>.geojson.
# meta.json lists each source's files, and the dashboard reads them from there.
KIND_FILENAMES = {"occupation": "polygons/occupation.geojson.gz", "kmz_layers": "polygons/occupation.geojson.gz",
                  "geoconfirmed": "points/events.geojson", "warspotting": "points/events.geojson",
                  "telegram_channel": "points/events.geojson", "war_fires": "points/fires.geojson.gz",
                  "telegram_posts": "posts/posts.geojson", "llm_summary": "text/summary.json",
                  "geo_analysis": "stats/facts.json"}


def build_reference(src):
    """One-time: copy OCHA's Ukraine boundaries (COD-AB v05, downloaded by hand from HDX into `src`) into ref/,
    unchanged but gzip-compressed: raions (admin 2) and settlement outlines (admin 4)."""
    for name in ("ukr_admin2.geojson", "ukr_admin4.geojson"):
        write_bytes(REF / f"{name}.gz", gz((Path(src) / name).read_bytes()))
    print("saved", *(f"{p.name} {p.stat().st_size // 1024} KB" for p in REF.glob("*.gz")))


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
    ap.add_argument("--build-reference", metavar="DIR", help="one-time: trim OCHA boundary files from DIR into ref/")
    ap.add_argument("--lookback", type=int, help="override every source's lookback_days (e.g. a one-time back-fill)")
    args = ap.parse_args()
    if args.build_reference:
        return build_reference(args.build_reference)

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
        cfg = {**SOURCES[sid], **({"lookback_days": args.lookback} if args.lookback else {})}
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
        # the map shows one checkbox per source listed here (the Posts tab: those with a "group"), even on empty days
        write_json(data / "sources.json", {"post_groups": POST_GROUPS, "sources": {
            k: {"name": v["name"], "url": v["url"], **({"group": v["group"]} if "group" in v else {})}
            for k, v in SOURCES.items() if v.get("enabled", True)}})
        # A day "has data" once at least one source folder exists under it (a source only gets a
        # folder once its file has been fully moved into place, so a half-finished run never counts).
        dates = sorted(p.name for p in data.iterdir() if p.is_dir() and any(c.is_dir() for c in p.iterdir()))
        write_json(data / "index.json", {"dates": dates, "updated_utc": now.isoformat(timespec="seconds")})
    shutil.rmtree(args.working_dir_path, ignore_errors=True)   # scratch space only; data/ already has the real copy
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()

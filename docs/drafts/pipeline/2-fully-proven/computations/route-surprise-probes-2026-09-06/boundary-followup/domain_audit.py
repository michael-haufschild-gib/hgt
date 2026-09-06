"""Separate the actual left-scale theorem domain from the earlier center-scale filter."""
import json
import mpmath as mp
mp.mp.dps = 80


with open("boundary-results.json") as f:
    old = json.load(f)
with open("slope-boundary.json") as f:
    slope = json.load(f)
out = {}
for physical in (True,False):
    selected = [r for r in old["results"] if (r["spec"][0] not in ("pi","4"))==physical]
    side = [r for x in selected for c in x.get("crossings",[]) for r in c["rows"]]
    srows = [r for r in slope["results"] if (r["spec"][0] not in ("pi","4"))==physical]
    eligible = [r for r in srows if r.get("gates")]
    out["left_scale_at_least_six" if physical else "extended_left_scale"] = dict(
        curvature_specs=len(selected),curvature_executed=sum("skip" not in r for r in selected),
        curvature_crossings=sum(len(r.get("crossings",[])) for r in selected),
        curvature_side_evaluations=len(side),curvature_admissible=sum(r["gates"] for r in side),
        slope_specs=len(srows),slope_bracketed=sum(not r.get("unbracketed",False) for r in srows),
        slope_admissible=len(eligible),
        smallest_slope_reserve=mp.nstr(10**min(mp.mpf(r["log10_curvature_ratio"]) for r in eligible),30))
with open("domain-audit.json","w") as f:
    json.dump(out,f,indent=2)
print(json.dumps(out,indent=2))

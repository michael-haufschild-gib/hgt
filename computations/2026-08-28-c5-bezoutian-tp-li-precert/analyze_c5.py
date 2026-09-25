import json, math
recs = []
for line in open("/root/precert/c5_grid.jsonl"):
    r = json.loads(line)
    if "error" in r: continue
    recs.append(r)
print("points:", len(recs))
# 1. interior minimum (t >= 0.25)
interior = [r for r in recs if r["t"] >= 0.25]
im = min(interior, key=lambda r: r["c5A2"])
print("interior min c5A2:", json.dumps(im))
# 2. boundary-normalized: c5A2 / t^4 for t < 0.25
bd = [r for r in recs if r["t"] < 0.25]
bm = min(bd, key=lambda r: r["c5A2"]/r["t"]**4)
print("boundary min c5A2/t^4:", im and json.dumps({**bm, "norm": bm["c5A2"]/bm["t"]**4}))
# distribution of normalized boundary coefficient vs u (t smallest slice)
tmin = min(r["t"] for r in recs)
slice0 = sorted([r for r in recs if abs(r["t"]-tmin)<1e-12], key=lambda r:r["u"])
prof = [(r["u"], r["c5A2"]/r["t"]**4) for r in slice0]
lo = min(prof, key=lambda p:p[1]); hi = max(prof, key=lambda p:p[1])
print(f"t={tmin:.4g} slice: min coeff {lo}, max coeff {hi}")
# 3. per-u interior minimum profile (sample)
import collections
byu = collections.defaultdict(list)
for r in interior: byu[r["u"]].append(r)
prof2 = []
for u in sorted(byu):
    m = min(byu[u], key=lambda r: r["c5A2"])
    prof2.append((u, m["t"], m["c5A2"]))
mins = sorted(prof2, key=lambda p:p[2])[:8]
print("8 tightest per-u interior minima (u, argmin t, c5A2):")
for p in mins: print("  ", p)
# 4. sanity: y range, identity checks relative
ymin = min(r["y"] for r in recs); ymax = max(r["y"] for r in recs)
print("y range:", ymin, ymax)
# 5. negative anywhere?
neg = [r for r in recs if r["c5A2"] < 0 or r["c5P2_sign"] < 0]
print("negatives:", len(neg))

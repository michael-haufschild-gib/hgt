#!/usr/bin/env python3.13
"""MWM engine v6 — R7 chunk 0: localize the off-line zeros of f_dh to small boxes.

For each seed box [s1,1.2]x[T,T+H] known to carry winding w>=1, bisect alternately in t
and sigma until the box is below (dt, ds), keeping a sub-box with nonzero winding.
Output: one JSON line per seed with the final center and box.

Usage: engine6.py localize S1 T1 T2 H [DT] [DS] [DPS]
(scans boxes [T, T+H) for T in [T1,T2) step H at sigma in (S1, 1.2); bisects each defect)
"""
import sys, json
from mpmath import mp, mpf
from engine2 import f_dh, winding

def bisect_box(s1, s2, t1, t2, dt, ds):
    w = winding(f_dh, s1, s2, t1, t2)
    if not w.get("ok") or w.get("w") in (0, None):
        return None
    while (t2 - t1) > dt or (s2 - s1) > ds:
        if (t2 - t1) > dt:
            tm = (t1 + t2) / 2
            wl = winding(f_dh, s1, s2, t1, tm)
            if wl.get("ok") and wl.get("w") not in (0, None):
                t2 = tm
            else:
                t1 = tm
        if (s2 - s1) > ds:
            sm = (s1 + s2) / 2
            wl = winding(f_dh, s1, sm, t1, t2)
            if wl.get("ok") and wl.get("w") not in (0, None):
                s2 = sm
            else:
                s1 = sm
    wf = winding(f_dh, s1, s2, t1, t2)
    return {"center": [float((s1 + s2) / 2), float((t1 + t2) / 2)],
            "box": [float(s1), float(s2), float(t1), float(t2)],
            "w": wf.get("w")}

if __name__ == "__main__":
    a = sys.argv[2:]
    mp.dps = int(a[6]) if len(a) > 6 else 20
    s1, t1, t2, H = mpf(a[0]), mpf(a[1]), mpf(a[2]), mpf(a[3])
    dt = mpf(a[4]) if len(a) > 4 else mpf("0.02")
    ds = mpf(a[5]) if len(a) > 5 else mpf("0.02")
    T = t1
    while T < t2:
        res = bisect_box(s1, mpf("1.2"), T, T + H, dt, ds)
        if res is not None:
            print(json.dumps(res), flush=True)
        T += H

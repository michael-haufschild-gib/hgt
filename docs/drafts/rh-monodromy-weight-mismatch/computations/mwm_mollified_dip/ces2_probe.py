#!/usr/bin/env python3
"""Doc 63 §6 pre-registered: P-CES2 (m=2 hull test) + P-CES1b (near-pass mechanism)."""
import numpy as np, json
from math import log, pi
rng = np.random.default_rng(632)
out = {}
for N in [40, 100, 200, 400]:
    logN = log(N); T0 = 2 * pi * (N + 0.25) ** 2
    lg = np.log(np.arange(1, N + 1, dtype=float))
    ks = np.arange(1, N + 1, dtype=float)
    def hp(pts):
        pts = pts[np.abs(pts) > 1e-14]
        ang = np.sort(np.angle(pts))
        gaps = np.diff(np.concatenate([ang, [ang[0] + 2 * pi]]))
        return bool(gaps.max() > pi + 1e-9)
    G = 60
    r1 = r2 = l1 = l2 = 0
    fails_m1 = []
    for _ in range(G):
        t0 = T0 + rng.uniform(0, 240.0)
        for side, sgn, cnt in (("R", 1, None), ("L", -1, None)):
            s0 = 0.5 + sgn * rng.uniform(0.1, 2.0) / logN + 1j * t0
            Z = np.cumsum(np.exp(-s0 * lg))
            C1 = np.cumsum(Z) / ks
            C2 = np.cumsum(C1) / ks
            h1, h2 = hp(C1[:-1]), hp(C2[:-1])
            if side == "R":
                r1 += h1; r2 += h2
                if not h1:
                    # P-CES1b: relative near-pass depth of the Cesaro path
                    theta = np.log(ks[1:])
                    rel = np.abs(C1[1:]) / np.sqrt(np.maximum(theta, 0.05))
                    fails_m1.append(float(rel.min()))
            else:
                l1 += h1; l2 += h2
    out[N] = {"grid": G, "right_m1": r1, "right_m2": r2,
              "left_m1": l1, "left_m2": l2, "m1_fail_reldepths": fails_m1}
    print(f"N={N}: right m1 {r1}/{G} m2 {r2}/{G} | left m1 {l1}/{G} m2 {l2}/{G} "
          f"| m1-fail rel-depths {['%.3f' % d for d in fails_m1]}", flush=True)
json.dump(out, open("ces2_probe.json", "w"), indent=1)

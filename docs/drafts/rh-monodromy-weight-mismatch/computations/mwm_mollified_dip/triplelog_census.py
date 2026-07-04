#!/usr/bin/env python3
"""Doc 64 §6 pre-registered P-TL census: hull-test fail rates vs N (no winding)."""
import numpy as np, json
from math import log, pi
rng = np.random.default_rng(64)
out = {}
for N in [40, 400, 4000, 40000]:
    logN = log(N); T0 = 2 * pi * (N + 0.25) ** 2
    lg = np.log(np.arange(1, N + 1, dtype=float))
    ks = np.arange(1, N + 1, dtype=float)
    def hp(pts):
        pts = pts[np.abs(pts) > 1e-14]
        ang = np.sort(np.angle(pts))
        gaps = np.diff(np.concatenate([ang, [ang[0] + 2 * pi]]))
        return bool(gaps.max() > pi + 1e-9)
    S = 1200
    f = {"R1": 0, "R2": 0, "L1": 0, "L2": 0}
    for _ in range(S):
        t0 = T0 + rng.uniform(0, 4000.0)
        for side, sgn in (("R", 1), ("L", -1)):
            s0 = 0.5 + sgn * rng.uniform(0.1, 2.0) / logN + 1j * t0
            Z = np.cumsum(np.exp(-s0 * lg))
            C1 = np.cumsum(Z) / ks
            C2 = np.cumsum(C1) / ks
            if not hp(C1[:-1]): f[side + "1"] += 1
            if not hp(C2[:-1]): f[side + "2"] += 1
    out[N] = {"samples": S, **f,
              "rates": {k: v / S for k, v in f.items()}}
    print(f"N={N}: fails/1200  R_m1={f['R1']} R_m2={f['R2']} "
          f"L_m1={f['L1']} L_m2={f['L2']}  loglogN={log(logN):.2f}", flush=True)
json.dump(out, open("triplelog_census.json", "w"), indent=1)

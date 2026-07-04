#!/usr/bin/env python3
"""Doc 62 §2.5 exploratory (UNREGISTERED) diagnostic: Cesaro m=1 hull test."""
import numpy as np, json
from math import log, pi
out = {}
rng = np.random.default_rng(625)
for N in [40, 100, 200, 400]:
    logN = log(N); T0 = 2 * pi * (N + 0.25) ** 2
    lg = np.log(np.arange(1, N + 1, dtype=float))
    def hp(pts):
        ang = np.sort(np.angle(pts))
        gaps = np.diff(np.concatenate([ang, [ang[0] + 2 * pi]]))
        return bool(gaps.max() > pi + 1e-9)
    r0 = r1 = l0 = l1 = 0
    G = 60
    for _ in range(G):
        t0 = T0 + rng.uniform(0, 240.0)
        for side, sgn in (("R", 1), ("L", -1)):
            s0 = 0.5 + sgn * rng.uniform(0.1, 2.0) / logN + 1j * t0
            Z = np.cumsum(np.exp(-s0 * lg))
            C1 = np.cumsum(Z) / np.arange(1, N + 1)      # Cesaro means
            if side == "R":
                r0 += hp(Z[:-1]); r1 += hp(C1[:-1])
            else:
                l0 += hp(Z[:-1]); l1 += hp(C1[:-1])
    out[N] = {"grid": G, "right_m0": r0, "right_m1": r1, "left_m0": l0, "left_m1": l1}
    print(f"N={N}: HP-pass right m0 {r0}/{G} m1 {r1}/{G} | left m0 {l0}/{G} m1 {l1}/{G}", flush=True)
json.dump(out, open("cesaro_diag.json", "w"), indent=1)

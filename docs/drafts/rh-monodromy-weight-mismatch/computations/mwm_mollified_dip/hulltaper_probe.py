#!/usr/bin/env python3
"""
Doc 64 §7 registered (HULL-taper) probe + plateau anti-concentration.
Carriers: plateau to N' = ceil(N/e), taper on (N', N]:
  lin:  A_n = log(N/n)/log(N/N')      (m=1-grade)
  cvx:  A_n = (log(N/n)/log(N/N'))^2  (m=2-grade)
Hull tests on the ARC mixture points {S_k : k in supp(dA)}; Cesaro-of-arc as
the m-dial refinement; plateau anti-concentration P(|S_{N'}| <= lam).
"""
import numpy as np, json
from math import log, pi, ceil
rng = np.random.default_rng(65)
out = {}
for N in [400, 4000, 40000]:
    logN = log(N); T0 = 2 * pi * (N + 0.25) ** 2
    Np = int(ceil(N / np.e))
    n = np.arange(1, N + 1, dtype=float)
    lg = np.log(n)
    ell = log(N / Np)
    prof = np.clip(np.log(N / n) / log(N / Np), 0, 1)
    A_lin = np.where(n <= Np, 1.0, prof)
    A_cvx = np.where(n <= Np, 1.0, prof ** 2)
    def hp(pts):
        pts = pts[np.abs(pts) > 1e-14]
        if len(pts) < 2: return True
        ang = np.sort(np.angle(pts))
        gaps = np.diff(np.concatenate([ang, [ang[0] + 2 * pi]]))
        return bool(gaps.max() > pi + 1e-9)
    S = 1500
    res = {"Nprime": Np, "ell": ell,
           "lin_m0": 0, "lin_m1": 0, "cvx_m0": 0, "cvx_m1": 0,
           "anchor_le": {0.5: 0, 1.0: 0, 2.0: 0}, "logNp": log(Np)}
    for _ in range(S):
        t0 = T0 + rng.uniform(0, 4000.0)
        s0 = 0.5 + rng.uniform(0.1, 2.0) / logN + 1j * t0
        Z = np.cumsum(np.exp(-s0 * lg))          # S_k, k = 1..N
        anchor = Z[Np - 1]
        for lam in (0.5, 1.0, 2.0):
            if abs(anchor) <= lam: res["anchor_le"][lam] += 1
        for tag, A in (("lin", A_lin), ("cvx", A_cvx)):
            dA = A[:-1] - A[1:]
            supp = np.where(dA > 1e-12)[0]       # indices i: weight on S_{i+2}? use S at i+1
            pts = Z[supp + 1]                    # mixture points S_{k+1}
            if A[-1] > 1e-12: pts = np.concatenate([pts, [Z[-1]]])
            res[tag + "_m0"] += (not hp(pts))
            ces = np.cumsum(pts) / np.arange(1, len(pts) + 1)
            res[tag + "_m1"] += (not hp(ces))
    res["rates"] = {k: res[k] / S for k in
                    ("lin_m0", "lin_m1", "cvx_m0", "cvx_m1")}
    res["anchor_rates"] = {str(k): v / S for k, v in res["anchor_le"].items()}
    out[N] = res
    print(f"N={N} N'={Np} ell={ell:.3f}: fails/1500 lin m0={res['lin_m0']} "
          f"m1={res['lin_m1']} cvx m0={res['cvx_m0']} m1={res['cvx_m1']} | "
          f"P(|S_Np|<=lam) {res['anchor_rates']} logNp={log(Np):.2f}", flush=True)
json.dump(out, open("hulltaper_probe.json", "w"), indent=1, default=str)

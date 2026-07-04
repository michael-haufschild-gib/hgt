#!/usr/bin/env python3
"""
Doc 62 §4 pre-registered sweep P-SC: mechanism test (mean-share vs order
structure) + HALF-PLANE diagnostic. N in {40,100,200,400}, alpha in {1,2,4},
U=240, CCW winding, both slivers; hull/half-plane test on sliver grids.
"""
import numpy as np, json
from math import log, pi

U = 240.0
NLIST = [40, 100, 200, 400]
ALPHAS = [1, 2, 4]

def run(N, alpha, rng):
    logN = log(N)
    T0 = 2 * pi * (N + 0.25) ** 2
    n = np.arange(1, N + 1, dtype=float)
    y = np.log(n) / logN
    a = np.sqrt((alpha + 1) * (1 - y) ** alpha)     # A_n, decreasing, A_N = 0
    lg = np.log(n)
    def F(s_arr):
        E = np.exp(-np.outer(np.atleast_1d(s_arr), lg))
        return (E * a[None, :]).sum(1)
    K = float((a ** 2 / n).sum())
    share = a[0] ** 2 / K

    def winding_ccw(b_lo, b_hi, t_lo, t_hi, ds=0.001):
        nt = max(24, int((t_hi - t_lo) / ds)); nb = max(24, int((b_hi - b_lo) / ds))
        pts = np.concatenate([
            np.linspace(b_lo, b_hi, nb) + 1j * t_lo,
            b_hi + 1j * np.linspace(t_lo, t_hi, nt),
            np.linspace(b_hi, b_lo, nb) + 1j * t_hi,
            b_lo + 1j * np.linspace(t_hi, t_lo, nt)])
        ph = np.unwrap(np.angle(F(pts)))
        return (ph[-1] - ph[0]) / (2 * pi)

    def band(b_lo, b_hi):
        tot = 0.0; bad = 0; t = T0
        while t < T0 + U:
            for _ in range(6):
                j = rng.uniform(0, 0.05)
                w = winding_ccw(b_lo, b_hi, t + j, t + j + 2)
                if abs(w - round(w)) < 0.05:
                    tot += round(w); break
            else:
                bad += 1
            t += 2.0
        return tot, bad

    res = {"share": share, "K": K}
    for c in (1, 2):
        wdt = c / logN
        r, br = band(0.5 + 1e-4, 0.5 + wdt)
        l, bl = band(0.5 - wdt, 0.5 - 1e-4)
        res[f"R{c}"], res[f"L{c}"], res[f"bad{c}"] = r, l, br + bl
    res["rateR2"] = res["R2"] / (U * logN)

    # HALF-PLANE diagnostic: 0 in conv{Z_n} iff all angular gaps < pi
    def halfplane_ok(s0):
        Z = np.cumsum(np.exp(-s0 * lg))            # Z_n(s0), n = 1..N
        pts = Z[:-1][a[:-1] - a[1:] > 1e-12]       # supp(DeltaA) = 1..N-1
        ang = np.sort(np.angle(pts))
        gaps = np.diff(np.concatenate([ang, [ang[0] + 2 * pi]]))
        return bool(gaps.max() > pi + 1e-9)        # True = half-plane exists = no hull
    hp = {"right_pass": 0, "left_pass": 0, "grid": 40}
    for _ in range(40):
        sig = 0.5 + rng.uniform(0.1, 2.0) / logN
        t0 = T0 + rng.uniform(0, U)
        hp["right_pass"] += halfplane_ok(sig + 1j * t0)
        sigL = 0.5 - rng.uniform(0.1, 2.0) / logN
        hp["left_pass"] += halfplane_ok(sigL + 1j * t0)
    res["halfplane"] = hp
    return res

rng = np.random.default_rng(62)
out = {}
for N in NLIST:
    for alpha in ALPHAS:
        r = run(N, alpha, rng)
        out[f"N{N}_a{alpha}"] = r
        print(f"N={N} a={alpha} share={r['share']:.3f} "
              f"R1={r['R1']:.0f} R2={r['R2']:.0f} L1={r['L1']:.0f} L2={r['L2']:.0f} "
              f"rateR2={r['rateR2']:.5f} bad={r['bad1']+r['bad2']} "
              f"HP right {r['halfplane']['right_pass']}/40 left {r['halfplane']['left_pass']}/40",
              flush=True)
json.dump(out, open("ek_sweep.json", "w"), indent=1)
print("\n=== P-SC1: R2 at alpha=2 across N (persist vs degrade) ===")
print([out[f"N{N}_a2"]["R2"] for N in NLIST], "shares:",
      [round(out[f"N{N}_a2"]["share"], 3) for N in NLIST])

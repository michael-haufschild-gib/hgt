#!/usr/bin/env python3
"""
Doc 61 §5 pre-registered probe P-SM: mean-share sweep for the chirality
mechanism. Carriers W_a^2(y) = (a+1)(1-y)^a, a in {0,1,2,4}; N=40; CCW winding
counts in right/left sliver bands c in {1,2}; predictions P-SM1/2/3 registered
in doc 61 BEFORE this run.
"""
import numpy as np, json
from math import log, pi, exp

N, U = 40, 240.0
T0 = 2 * pi * (N + 0.25) ** 2
logN = log(N)
ALPHAS = [0, 1, 2, 4]

def coeffs(alpha):
    n = np.arange(1, N + 1, dtype=float)
    y = np.log(n) / logN
    W2 = (alpha + 1) * (1 - y) ** alpha
    return np.sqrt(W2)          # a_n multiplying n^{-s}

def make_F(a):
    n = np.arange(1, N + 1, dtype=float)
    lg = np.log(n)
    def F(s_arr):
        E = np.exp(-np.outer(np.atleast_1d(s_arr), lg))
        return (E * a[None, :]).sum(1)
    return F

def winding_ccw(F, b_lo, b_hi, t_lo, t_hi, ds=0.001):
    nt = max(24, int((t_hi - t_lo) / ds)); nb = max(24, int((b_hi - b_lo) / ds))
    pts = np.concatenate([
        np.linspace(b_lo, b_hi, nb) + 1j * t_lo,   # bottom, rightward
        b_hi + 1j * np.linspace(t_lo, t_hi, nt),   # right, upward
        np.linspace(b_hi, b_lo, nb) + 1j * t_hi,   # top, leftward
        b_lo + 1j * np.linspace(t_hi, t_lo, nt)])  # left, downward
    ph = np.unwrap(np.angle(F(pts)))
    return (ph[-1] - ph[0]) / (2 * pi)

def band_count(F, b_lo, b_hi, rng):
    tot = 0.0; bad = 0
    t = T0
    while t < T0 + U:
        for _ in range(6):
            j = rng.uniform(0, 0.05)
            w = winding_ccw(F, b_lo, b_hi, t + j, t + j + 2)
            if abs(w - round(w)) < 0.05:
                tot += round(w); break
        else:
            bad += 1
        t += 2.0
    return tot, bad

rng = np.random.default_rng(61)
out = {}
for alpha in ALPHAS:
    a = coeffs(alpha)
    F = make_F(a)
    K = float((a ** 2 / np.arange(1, N + 1)).sum())     # K(1/2)
    m2 = float(a[0] ** 2)
    pred_supp = exp(-m2 / (K - m2))
    res = {"K_half": K, "mean_share": m2 / K, "pred_supp": pred_supp}
    for c in (1, 2):
        w = c / logN
        r, badr = band_count(F, 0.5 + 1e-4, 0.5 + w, rng)
        l, badl = band_count(F, 0.5 - w, 0.5 - 1e-4, rng)
        res[f"right_c{c}"] = r; res[f"left_c{c}"] = l
        res[f"bad_c{c}"] = badr + badl
    out[alpha] = res
    print(f"alpha={alpha} share={m2/K:.3f} pred_supp={pred_supp:.3f} "
          f"R(c=1)={res['right_c1']:.0f} R(c=2)={res['right_c2']:.0f} "
          f"L(c=1)={res['left_c1']:.0f} L(c=2)={res['left_c2']:.0f} "
          f"bad={res['bad_c1']+res['bad_c2']}")

# adjudication lines
sharp = out[0]
print("\n=== P-SM adjudication ===")
rs = [out[a]["right_c2"] for a in ALPHAS]
print("P-SM1 right_c2 by alpha:", rs, "monotone_dec:", all(rs[i] >= rs[i+1] for i in range(len(rs)-1)))
for a in ALPHAS[1:]:
    meas = (out[a]["right_c2"] + 0.5) / (sharp["right_c2"] + 0.5)
    pred = out[a]["pred_supp"] / sharp["pred_supp"]
    print(f"P-SM2 alpha={a}: meas_supp={meas:.3f} pred={pred:.3f} ratio={meas/pred:.2f}")
for a in ALPHAS:
    tot = out[a]["right_c2"] + out[a]["left_c2"]
    var = (a + 1) / ((a + 2) ** 2 * (a + 3))    # Beta(1, a+1): Var_mu
    print(f"P-SM3 alpha={a}: twosided_c2={tot:.0f} Var_mu={var:.4f} "
          f"tot/Var={tot/var:.0f}")
json.dump(out, open("meanshare_probe.json", "w"), indent=1, default=str)

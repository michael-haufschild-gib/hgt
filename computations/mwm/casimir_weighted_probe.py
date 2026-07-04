#!/usr/bin/env python3
"""Weighted-carrier test of the VARIANCE LAW (doc 55 §8) — the Casimir rabbit hole.

Analytic result (proved, this cycle): in the matched limit the GAF near-line
intensity of F_W(s) = sum_n W(log n/log N) n^{-s} is governed by the log-placement
measure mu ~ W(y)^2 dy on [0,1]:
    eps_W'(0) = Var_mu(Y)/pi,   eps_W(inf) = E_mu[Y]/(2pi)  (right-of-line share).
Sharp cut => mu uniform => Var 1/12 (the "Casimir" 1/12 = variance of uniform).

THIS PROBE tests whether the DETERMINISTIC F_W follows the variance law (the
GAF-comparison, the open core), using carriers with equal variance but opposite
edges, and unequal means.

Carriers: sharp W^2=1 (Var 1/12, mean 1/2); ramp W^2=2y (Var 1/18, mean 2/3);
iramp W^2=2(1-y) (Var 1/18, mean 1/3).

PRE-REGISTERED PREDICTIONS (before run):
  P-CAS1 (prior 0.55): per-band counts match the FINITE-N GAF prediction
        (U/4pi)[(logK)'(1/2+c/logN)-(logK)'(1/2)] within x[0.6,1.6];
        in particular slope_ramp/slope_sharp ~ (1/18)/(1/12) = 2/3 +- 0.25.
  P-CAS2 (prior 0.60): ramp and iramp show the SAME near-line counts (equal Var)
        despite opposite multiplicative edges. Falsified => variance law dead.
  P-CAS3 (prior 0.70): right:left zero split ~ mean: ramp 2/3 right,
        iramp 1/3 right, sharp 1/2.
Falsification of P-CAS2/3 kills the GAF-dictionary lead; confirmation = strong lead.
"""
import sys
from mpmath import mp, mpc, mpf, pi, log, im, re

mp.dps = 25


def make_F(N, W2):
    L = float(log(N))
    ws = [None] * (N + 1)
    for n in range(1, N + 1):
        y = float(log(n)) / L
        w2 = W2(y)
        ws[n] = mp.sqrt(w2) if w2 > 0 else mpf(0)

    def F(s):
        return sum(ws[n] * mpf(n) ** (-s) for n in range(1, N + 1) if ws[n] != 0)
    return F, ws


def winding(g, s_lo, s_hi, t_lo, t_hi, m=200):
    pts = []
    for k in range(m):
        pts.append(mpc(s_lo + (s_hi - s_lo) * k / m, t_lo))
    for k in range(m):
        pts.append(mpc(s_hi, t_lo + (t_hi - t_lo) * k / m))
    for k in range(m):
        pts.append(mpc(s_hi - (s_hi - s_lo) * k / m, t_hi))
    for k in range(m):
        pts.append(mpc(s_lo, t_hi - (t_hi - t_lo) * k / m))
    pts.append(pts[0])
    tot = mpf(0)
    prev = g(pts[0])
    for p in pts[1:]:
        cur = g(p)
        d = cur / prev
        tot += mp.atan2(im(d), re(d))
        prev = cur
    return int(round(float(tot / (2 * pi))))


def dlogK(ws, N, sig):
    h = mpf(10) ** (-10)
    Kp = sum(ws[n] ** 2 * mpf(n) ** (-2 * (sig + h)) for n in range(1, N + 1) if ws[n] != 0)
    Km = sum(ws[n] ** 2 * mpf(n) ** (-2 * (sig - h)) for n in range(1, N + 1) if ws[n] != 0)
    return (mp.log(Kp) - mp.log(Km)) / (2 * h)


CARRIERS = [
    ('sharp', lambda y: 1.0),          # Var 1/12, mean 1/2
    ('ramp',  lambda y: 2.0 * y),      # Var 1/18, mean 2/3
    ('iramp', lambda y: 2.0 * (1.0 - y)),  # Var 1/18, mean 1/3
]

if __name__ == '__main__':
    U = mpf(60)
    half = mpf('0.5')
    for N in [28, 40]:
        T = mpf(2) * pi * (N + mpf('0.5')) ** 2
        L = float(log(N))
        print(f"== N={N} T={float(T):.1f} logN={L:.3f} U={float(U)}")
        for name, W2 in CARRIERS:
            F, ws = make_F(N, W2)
            # finite-N GAF predictions
            d_half = dlogK(ws, N, half)
            preds = {}
            for c in [0.5, 1.0, 2.0]:
                d_c = dlogK(ws, N, half + mpf(c) / L)
                preds[c] = float(U / (4 * pi) * (d_c - d_half))
            d_R = dlogK(ws, N, half + 4)
            d_Lf = dlogK(ws, N, half - 4)
            pred_right = float(U / (4 * pi) * (d_R - d_half))
            pred_left = float(U / (4 * pi) * (d_half - d_Lf))
            # deterministic winding counts
            cnts = {}
            for c in [0.5, 1.0, 2.0]:
                cnts[c] = winding(F, half, half + mpf(c) / L, T, T + U)
            cnt_right = winding(F, half, half + 4, T, T + U)
            cnt_left = winding(F, half - 4, half, T, T + U)
            bandstr = "  ".join(
                f"c={c}: {cnts[c]}/{preds[c]:.2f}" for c in [0.5, 1.0, 2.0])
            tot = cnt_right + cnt_left
            frac = cnt_right / tot if tot else float('nan')
            print(f"  {name:<6} bands(det/GAF): {bandstr}   "
                  f"R:L={cnt_right}:{cnt_left} (fracR={frac:.3f}; "
                  f"GAF {pred_right:.1f}:{pred_left:.1f})")
            sys.stdout.flush()
    print("done")

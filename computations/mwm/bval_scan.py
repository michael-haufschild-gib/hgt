#!/usr/bin/env python3
"""
Doc 46 SS6: DIRECT instance test of (BVAL) — the irreducible statement.

Scan B = Phi_{N-1} (one-term-under-resolved) over the p-central stretch
p in [0.2, 0.8] of interval N, sigma in [0.55, 0.80], t-step 0.1: record
min over the stretch of ratio(s) := |B(s)| / (2 |gamma(s)| N^{-1/2})
(a (BVAL)-violating valley has ratio <= ~1 at some off-line point).
Intervals: N = 22 (t in [3097, 3253]) and N = 35 (t in [7787, 8052]).

PRE-REGISTERED:
  P-V1 (prior 0.60): min ratio > 1 on BOTH stretches (no (BVAL)-violating
       off-line valleys at p-central; the irreducible statement gets its first
       direct census).
  FAIL branch: a deep valley WITHOUT a pair exists => (BVAL) as stated is too
       strong; the true statement is joint (depth AND phase-match) — re-cut.
"""
from mpmath import mp, mpc, mpf, pi, fabs, gamma as Gamma
from euler_suppression_boxcount import make_phi, coeffs
mp.dps = 25
NC = 50
for N in (22, 35):
    a = coeffs('E', 0, NC)
    B = make_phi(a, N - 1)
    tlo = float(2 * pi * (N + mpf('0.2')) ** 2)
    thi = float(2 * pi * (N + mpf('0.8')) ** 2)
    best, arg = None, None
    t = mpf(tlo)
    while t < thi:
        for sg in ('0.55', '0.60', '0.65', '0.70', '0.75', '0.80'):
            s = mpc(mpf(sg), t)
            ratio = fabs(B(s)) / (2 * fabs(pi ** (-s/2) * Gamma(s/2))
                                  * mpf(N) ** mpf('-0.5'))
            if best is None or ratio < best:
                best, arg = ratio, (float(t), sg)
        t += mpf('0.1')
    print(f"N={N}: p-central stretch t in [{tlo:.0f},{thi:.0f}] "
          f"({int((thi-tlo)/0.1)} t-steps x 6 sigma): min ratio = "
          f"{float(best):.3f} at t={arg[0]:.2f}, sigma={arg[1]}  "
          f"{'PASS' if best > 1 else 'VIOLATION'}")

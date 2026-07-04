#!/usr/bin/env python3
"""
Doc 45 SS4 opening (1): the push-sign profile sigma(p) on UNIFORM p-grids
(selection-free test of the resonant-attraction mechanism).

For N in {22, 35}: interval t in [2 pi N^2, 2 pi (N+1)^2). Homotopy in the
marginal term: A_lam = A_{N-1} + lam N^{-s}, exact-FE symmetrization. Uniform
grid p in {.05,.1,...,.95}; for each p, THREE windows (centers t(p) + {-9,0,+9})
of half-width 3; statistic per window: Dming = mingap(lam=1) - mingap(lam=0)
of on-line zeros. Note first-order push theory predicts NO systematic
p-dependence at fixed height (push phase frozen in lam); the film's attraction
could be survivor-selection. This run decides.

PRE-REGISTERED:
  P-S1 (prior 0.55): mean Dming < 0 on p in (0,.15] and mean Dming > 0 on
       p in [.3,.7], in BOTH intervals (resonant attraction is mechanism,
       not selection).
  FAIL branch: Dming profile flat/noisy in p ==> the p-localization of births
       is configurational (soft gaps) + selection; re-aim (MID-central) at the
       softness statistic, not the phase.
"""
from mpmath import mp, mpc, mpf, pi, re, gamma as Gamma
mp.dps = 25

def make_phi_lam(N, lam):
    def A(s):
        return sum(mpf(n) ** (-s) for n in range(1, N)) + lam * mpf(N) ** (-s)
    def phi(s):
        return (pi ** (-s / 2) * Gamma(s / 2) * A(s)
                + pi ** (-(1 - s) / 2) * Gamma((1 - s) / 2) * A(1 - s))
    return phi

def mingap(phi, tc, hw):
    Z = lambda t: re(phi(mpc(mpf('0.5'), t)))
    ts = [tc - hw + mpf('0.06') * k for k in range(int(2 * hw / 0.06) + 1)]
    vals = [Z(t) for t in ts]
    zs = []
    for i in range(len(ts) - 1):
        if vals[i] * vals[i + 1] < 0:
            lo, hi = ts[i], ts[i + 1]
            for _ in range(25):
                mid = (lo + hi) / 2
                if Z(lo) * Z(mid) <= 0:
                    hi = mid
                else:
                    lo = mid
            zs.append((lo + hi) / 2)
    gaps = [zs[i + 1] - zs[i] for i in range(len(zs) - 1)]
    return min(gaps) if gaps else None

for N in (22, 35):
    print(f"== N = {N}, interval [{float(2*pi*N**2):.0f}, {float(2*pi*(N+1)**2):.0f})")
    lo_band, mid_band = [], []
    for k in range(1, 20):
        p = mpf(k) / 20
        tc0 = 2 * pi * (N + p) ** 2
        ds = []
        for off in (-9, 0, 9):
            tc = tc0 + off
            g0 = mingap(make_phi_lam(N, mpf(0)), tc, mpf(3))
            g1 = mingap(make_phi_lam(N, mpf(1)), tc, mpf(3))
            if g0 is not None and g1 is not None:
                ds.append(float(g1 - g0))
        m = sum(ds) / len(ds) if ds else float('nan')
        tag = ''
        if float(p) <= 0.15:
            lo_band += ds; tag = ' [lo]'
        if 0.3 <= float(p) <= 0.7:
            mid_band += ds; tag = ' [mid]'
        print(f"  p={float(p):.2f}: mean Dming = {m:+.4f}  ({len(ds)} windows){tag}")
    mlo = sum(lo_band) / len(lo_band)
    mmid = sum(mid_band) / len(mid_band)
    print(f"  N={N}: lo-band mean = {mlo:+.4f}  mid-band mean = {mmid:+.4f}  "
          f"{'P-S1-half PASS' if (mlo < 0 < mmid) else 'P-S1-half FAIL'}")

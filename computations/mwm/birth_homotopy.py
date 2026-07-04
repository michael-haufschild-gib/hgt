#!/usr/bin/env python3
"""
Doc 44 SS4 opening (2) — the birth mechanism (task #130, (MID-central)).

Homotopy in the MARGINAL term: A_lam(s) = sum_{n<=34} n^-s + lam*35^-s,
Phi_lam = gamma(s)A_lam(s) + gamma(1-s)A_lam(1-s)  (exact FE, real, every lam).
The two N = 35 mid-band survivors (t0 = 7712.85, 7734.71; p = .036, .086) sit
just above the n = 35 entry at t* = 2*pi*35^2 = 7696.9. Control: p-central
height t = 7900 (p ~ 0.45) in the same interval.

Per (height, lam in {0,.2,.4,.6,.8,1}): (a) box winding [0.53,1.35] x [t0-2.5,
t0+2.5] (pair present?); (b) on-line zeros in [t0-3, t0+3] and the minimal
consecutive gap (collision watch); (c) refine the pair if present (eta(lam)).

PRE-REGISTERED:
  P-B1 (prior 0.60): both survivors' pairs are ABSENT at lam = 0 and PRESENT at
       lam = 1 — created by the marginal resonant term.
  P-B2 (prior 0.60): along lam, two flanking on-line zeros' gap shrinks to a
       collision at some lam* in (0,1) where the pair emerges (collision birth).
  P-B3 (prior 0.70): control at p ~ 0.45: no pair at ANY lam (marginal-term
       entry harmless at p-central heights).
"""
from mpmath import mp, mpc, mpf, pi, re, im, fabs, findroot, gamma as Gamma
from euler_suppression_boxcount import winding

mp.dps = 30

def make_phi_lam(lam):
    def A(s):
        return sum(mpf(n) ** (-s) for n in range(1, 35)) + lam * mpf(35) ** (-s)
    def phi(s):
        return (pi ** (-s / 2) * Gamma(s / 2) * A(s)
                + pi ** (-(1 - s) / 2) * Gamma((1 - s) / 2) * A(1 - s))
    return phi

def online_zeros(phi, t0, halfw):
    Z = lambda t: re(phi(mpc(mpf('0.5'), t)))
    ts = [t0 - halfw + mpf('0.05') * k for k in range(int(2 * halfw / 0.05) + 1)]
    vals = [Z(t) for t in ts]
    zs = []
    for i in range(len(ts) - 1):
        if vals[i] * vals[i + 1] < 0:
            lo, hi = ts[i], ts[i + 1]
            for _ in range(35):
                mid = (lo + hi) / 2
                if Z(lo) * Z(mid) <= 0:
                    hi = mid
                else:
                    lo = mid
            zs.append(float((lo + hi) / 2))
    return zs

HEIGHTS = [(mpf('7712.85'), 'survivor-1 (p=.036)'),
           (mpf('7734.71'), 'survivor-2 (p=.086)'),
           (mpf('7900.0'), 'control (p~.45)')]

for t0, tag in HEIGHTS:
    print(f"== {tag}, t0 = {float(t0)}")
    for lamس in ('0', '0.2', '0.4', '0.6', '0.8', '1'):
        lam = mpf(lamس)
        phi = make_phi_lam(lam)
        w, susp = winding(phi, mpf('0.53'), mpf('1.35'), t0 - mpf('2.5'),
                          t0 + mpf('2.5'), m=160)
        if susp:
            w, _ = winding(phi, mpf('0.53'), mpf('1.35'), t0 - mpf('2.5'),
                           t0 + mpf('2.5'), m=320)
        zs = online_zeros(phi, t0, mpf(3))
        gaps = [zs[i+1] - zs[i] for i in range(len(zs) - 1)]
        mingap = min(gaps) if gaps else float('nan')
        eta = ''
        if w != 0:
            try:
                r = findroot(phi, mpc('0.62', t0), solver='muller',
                             tol=mpf('1e-25'))
                if mpf('0.53') < re(r) < mpf('1.35'):
                    eta = f" eta={float(re(r))-0.5:.3f}"
            except Exception:
                pass
        print(f"  lam={lamس}: pairs={w}  onlineZ={len(zs)}  "
              f"mingap={mingap:.3f}{eta}")

#!/usr/bin/env python3
"""
(DISC-fin) first finite window-relation instance -- task #136, doc 22 SS4.

PRE-REGISTERED PREDICTIONS (before first run):
  g_N(s) = sum_{n<=N} n^{-s} + chix(s) sum_{n<=N} n^{s-1}, N = floor(sqrt(T/2pi)).
  Completed carrier: Xi_g(t) = Re[ pi^{-s/2} Gamma(s/2) g_N(s) ], s = 1/2+it
  (real on the line because g_N satisfies zeta's EXACT chi-FE).
  PA2: carrier reality |Im|/|.| < 1e-15 on sample points.
  PL (prior 0.75): the strip scan sigma in [0.55,1.2], t in [430,470]u[980,1020]
      finds >= 1 off-line zero of g_N (Spira: RS-length truncations have them).
  PM (prior 0.65): at a found zero (beta+i*gamma0, beta>0.52), the recentered jet
      reader (d in {4,6,8}, n=0) on Xi_g at t0=gamma0 counts non-real pairs
      == direct off-line zero count in the window, i.e. disc sign reads the
      truncation's local square class.
  FALSIFIER: reader misreads (0 when zeros present / >=2 spurious) -> (DISC-fin)
      shape dead on truncations.
"""
from mpmath import mp, mpc, mpf, zeta, gamma as Gamma, pi, sin, cos, floor, sqrt, fabs, diff, binomial, polyroots, re, im, findroot

mp.dps = 50
i = mpc(0, 1)


def chix(s):
    return 2 ** s * pi ** (s - 1) * sin(pi * s / 2) * Gamma(1 - s)


def make_g(N):
    def g(s):
        a = sum(mpf(n) ** (-s) for n in range(1, N + 1))
        b = sum(mpf(n) ** (s - 1) for n in range(1, N + 1))
        return a + chix(s) * b
    return g


def scan_offline(g, t_lo, t_hi):
    found = []
    t = mpf(t_lo)
    while t < t_hi:
        sig = mpf('0.55')
        while sig < mpf('1.2'):
            s0 = mpc(sig, t)
            if fabs(g(s0)) < mpf('0.35'):
                try:
                    r = findroot(g, s0, solver='muller', tol=mpf('1e-30'))
                    if re(r) > mpf('0.52') and t_lo - 1 < im(r) < t_hi + 1:
                        if all(fabs(r - q) > mpf('1e-6') for q in found):
                            found.append(r)
                except Exception:
                    pass
            sig += mpf('0.05')
        t += mpf('0.25')
    return found


def carrier(g):
    def Xi(t):
        s = mpf(1) / 2 + i * t
        return pi ** (-s / 2) * Gamma(s / 2) * g(s)
    return Xi


def reader(Xi, t0):
    gam = [re(diff(Xi, t0, m, direction=0)) for m in range(10)]
    out = {}
    for d in (4, 6, 8):
        coeffs = [binomial(d, j) * gam[j] for j in range(d, -1, -1)]
        roots = polyroots(coeffs, maxsteps=200, extraprec=200)
        nr = sum(1 for r in roots if fabs(im(r)) / (1 + fabs(r)) > mpf('1e-25'))
        out[d] = nr // 2
    return out


if __name__ == "__main__":
    for T0, T1 in ((430, 470), (980, 1020)):
        N = int(floor(sqrt(mpf(T0 + T1) / 2 / (2 * pi))))
        g = make_g(N)
        Xi = carrier(g)
        w = max(fabs(im(Xi(mpf(t)))) / fabs(Xi(mpf(t))) for t in (T0 + mpf('0.3'), (T0 + T1) / 2))
        print(f"[T~{T0}-{T1}] N={N}  PA2 |Im|/|Xi| = {mp.nstr(w, 3)} {'PASS' if w < mpf('1e-15') else 'FAIL'}")
        zs = scan_offline(g, T0, T1)
        print(f"  off-line zeros found: {[(mp.nstr(re(z), 8), mp.nstr(im(z), 10)) for z in zs]}")
        for z in zs:
            t0 = im(z)
            counts = reader(Xi, t0)
            # direct window count: off-line zeros within |Im - t0| < 1.0 (right half)
            nw = sum(1 for q in zs if fabs(im(q) - t0) < 1)
            print(f"  zero at beta={mp.nstr(re(z), 8)}, t0={mp.nstr(t0, 10)}: "
                  f"reader d->pairs {counts} | direct right-half count in |dt|<1: {nw}")

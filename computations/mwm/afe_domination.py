#!/usr/bin/env python3
"""
(ANNEAL) calibration: AFE-truncation domination on window boundaries — task #134,
doc 22.

g_N(s) = sum_{n<=N} n^{-s} + chix(s) * sum_{n<=N} n^{s-1},
chix(s) = 2^s pi^{s-1} sin(pi s/2) Gamma(1-s),  N = floor(sqrt(T/(2 pi))).
g_N satisfies the EXACT functional equation g_N(1-s) = chix(1-s) g_N(s)
(since chix(s) chix(1-s) = 1) — it carries the FE structure of the truncation.

PRE-REGISTERED PREDICTIONS (before first run):
  Windows: center 1/2 + iT, radii r in {0.20, 0.35}, 96 boundary samples.
  T values: 1000 fixed + rng-drawn from [300, 3000] (recorded below at run time).
  q := max over circle of |zeta - g_N| / |g_N|.
  PE: q < 1 (domination) on >= 75% of the r=0.20 circles;
      failures correlate with a near-zero of g_N on the circle
      (min |g_N| < 0.05 * median |g_N|).
  PF: r=0.35 systematically worse than r=0.20 (AFE error grows off-line like
      x^{-sigma} + t^{1/2-sigma} y^{sigma-1}).
  Purpose: calibration ONLY (exceptional-set size); domination is expected to hold
  off a sparse set — the content is HOW sparse at accessible heights.
"""
import sys
from mpmath import mp, mpc, mpf, zeta, gamma as Gamma, pi, sin, floor, sqrt, fabs, exp, cos

mp.dps = 30

i = mpc(0, 1)


def chix(s):
    return 2 ** s * pi ** (s - 1) * sin(pi * s / 2) * Gamma(1 - s)


def g_N(s, N):
    a = sum(mpf(n) ** (-s) for n in range(1, N + 1))
    b = sum(mpf(n) ** (s - 1) for n in range(1, N + 1))
    return a + chix(s) * b


def probe(T, r, M=96):
    N = int(floor(sqrt(T / (2 * pi))))
    c = mpf(1) / 2 + i * T
    qmax = mpf(0)
    gvals = []
    for k in range(M):
        th = 2 * pi * k / M
        s = c + r * (cos(th) + i * sin(th))
        gv = g_N(s, N)
        zv = zeta(s)
        gvals.append(fabs(gv))
        q = fabs(zv - gv) / fabs(gv)
        qmax = max(qmax, q)
    gs = sorted(gvals)
    med = gs[len(gs) // 2]
    return N, qmax, gs[0], med


if __name__ == "__main__":
    Ts = [int(x) for x in sys.argv[1:]] or [1000]
    print("T        r     N   qmax        min|g|      med|g|    dominated")
    for T in Ts:
        for r in (mpf('0.20'), mpf('0.35')):
            N, qmax, gmin, gmed = probe(mpf(T), r)
            print(f"{T:<8d} {float(r):<5.2f} {N:<3d} {float(qmax):<11.4g} "
                  f"{float(gmin):<11.4g} {float(gmed):<9.4g} {'YES' if qmax < 1 else 'no'}")

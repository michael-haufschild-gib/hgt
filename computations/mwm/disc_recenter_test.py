#!/usr/bin/env python3
"""
(DISC) recentered-section test — task #132, doc 20. Follow-up to disc_spur_test.py.

FINDING FROM RUNS 1-2: global sections see a non-real pair only if d >= c*|pair
location|; the shift index n does NOT re-center the view (pairs at zero-index >= 2
invisible for all d <= 40, n <= 24).

PRE-REGISTERED PREDICTIONS (before this run):
  Recenter the carrier at x0 = 60: G(h) = F(60+h), F = (x-(60+8i))(x-(60-8i))cos(sqrt x),
  so the quadratic factor becomes EXACTLY h^2 + 64 (pair at h = +-8i, distance 8).
  Control: G0(h) = (h^2 - 64) cos(sqrt(60+h)) (real pair at h = +-8).
  P5: witness pair count = 1 for d above a SMALL threshold (~8-16) at small n
      (visibility scale = recentered distance 8, not the global coordinate 60).
  P6: no spurious pairs anywhere (counts in {0,1}); control all 0.
  FALSIFIER: pair invisible at all d <= 40 after recentering kills the
  "recentering = localization" dictionary.
Exact rational recentering: cos(sqrt(60+h)) = sum_m b_m h^m,
  b_m = sum_{k>=m} (-1)^k C(k,m) 60^(k-m) / (2k)!   (truncated at k <= 200, exact).
"""
from fractions import Fraction
from math import comb
import mpmath as mp

mp.mp.dps = 80
KMAX = 200
MMAX = 60


def cos_sqrt_recentered(x0):
    fact2 = [Fraction(1)]
    for i in range(1, 2 * KMAX + 1):
        fact2.append(fact2[-1] * i)
    b = []
    for m in range(MMAX + 1):
        s = Fraction(0)
        for k in range(m, KMAX + 1):
            s += Fraction((-1) ** k) * comb(k, m) * Fraction(x0) ** (k - m) / fact2[2 * k]
        b.append(s)
    return b


def pair_count(gamma, d, n):
    coeffs = []
    for j in range(d, -1, -1):
        c = Fraction(comb(d, j)) * gamma[n + j]
        coeffs.append(mp.mpf(c.numerator) / mp.mpf(c.denominator))
    while coeffs and coeffs[0] == 0:
        coeffs = coeffs[1:]
    if len(coeffs) <= 1:
        return 0
    roots = mp.polyroots(coeffs, maxsteps=300, extraprec=300)
    nonreal = sum(1 for r in roots if abs(mp.im(r)) / (1 + abs(r)) > mp.mpf('1e-40'))
    assert nonreal % 2 == 0
    return nonreal // 2


def run(label, quad_const, b):
    # G(h) = (h^2 + quad_const) * cos(sqrt(60+h)); g_m = quad_const*b_m + b_{m-2}
    g = []
    for m in range(MMAX + 1):
        v = Fraction(quad_const) * b[m]
        if m >= 2:
            v += b[m - 2]
        g.append(v)
    gamma, f = [], Fraction(1)
    for m in range(MMAX + 1):
        gamma.append(f * g[m])
        f *= (m + 1)
    print(f"== {label} ==")
    ds = [4, 6, 8, 10, 14, 20, 30, 40]
    ns = list(range(0, 13))
    print("d\\n " + " ".join(f"{n:2d}" for n in ns))
    worst = 0
    for d in ds:
        row = []
        for n in ns:
            c = pair_count(gamma, d, n)
            worst = max(worst, c)
            row.append(c)
        print(f"d={d:2d} " + " ".join(f"{c:2d}" for c in row))
    print(f"max pair count = {worst}")
    return worst


if __name__ == "__main__":
    b = cos_sqrt_recentered(60)
    w = run("WITNESS recentered: (h^2+64) cos(sqrt(60+h))  [pair at +-8i]", 64, b)
    c = run("CONTROL  recentered: (h^2-64) cos(sqrt(60+h))  [real pair +-8]", -64, b)
    print()
    print(f"P5 (witness visible at small d): {'PASS' if w >= 1 else 'FAIL'}")
    print(f"P6 (control all zero):           {'PASS' if c == 0 else 'FAIL'}")

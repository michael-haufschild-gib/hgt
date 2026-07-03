#!/usr/bin/env python3
"""
(SPUR) synthetic node test — task #132, doc 20 (DISC dictionary).

PRE-REGISTERED PREDICTIONS (before first run):
  Model: g(x) = cos(sqrt(x))  [LP-type: real entire, zeros x_k = ((2k+1)pi/2)^2 > 0:
         2.47, 22.2, 61.7, 121.0, 200.0, ...]
  Witness: F = P*g, P = (x-tau)(x-taubar), tau = 10+4i  (one simple non-real pair,
         sitting between zero #0 and zero #1 of g).
  Control: F0 = P0*g, P0 = (x-6)(x-14)  (same scale, real roots -> F0 has ONLY real
         zeros, F0 in LP  => Jensen sections hyperbolic by Jensen's theorem).

  Jensen sections: J^{d,n}(X) = sum_j C(d,j) * gamma(n+j) * X^j,  gamma(m) = m! c_m.
  Exact three-term shift identity (derived in doc 20 SS2):
      gamma_{P*g}(m) = |tau|^2 gamma_g(m) - 2a m gamma_g(m-1) + m(m-1) gamma_g(m-2).

  P1 (control): non-real pair count = 0 for ALL (d,n) tested.        [validates code]
  P2 (witness, no spurious pairs): pair count in {0,1} for all (d,n); never >= 2.
  P3 (witness, visibility band): count = 1 in a contiguous band of small n
      (the pair has zero-index ~1) for d large enough; count = 0 for n beyond a
      threshold (Polya-Wiman forgetting: high-shift sections look past the pair).
  FALSIFIER: robust count >= 2 anywhere kills the clean (DISC) dictionary shape.

Grid: d in {4,6,8,10,14,20,30,40}, n in 0..24. Exact rational coefficients
(fractions), rootfinding at mp.dps=60, non-real tolerance |Im|/(1+|root|) > 1e-30.
"""
from fractions import Fraction
import mpmath as mp

mp.mp.dps = 60

MMAX = 100  # need gamma up to n+d <= 24+40+2


def gamma_g(m):
    # cos(sqrt(x)) = sum (-1)^m x^m/(2m)!  => gamma(m) = (-1)^m m!/(2m)!
    if m < 0:
        return Fraction(0)
    num = Fraction((-1) ** m)
    f = Fraction(1)
    for i in range(m + 1, 2 * m + 1):
        f *= i
    return num / f  # m!/(2m)! = 1/prod_{m+1}^{2m}


def gamma_quad_times_g(m, two_a, mod2):
    # P = x^2 - two_a*x + mod2  (roots tau,taubar with 2a=two_a, |tau|^2=mod2)
    return (Fraction(mod2) * gamma_g(m)
            - Fraction(two_a) * m * gamma_g(m - 1)
            + Fraction(m * (m - 1)) * gamma_g(m - 2))


def pair_count(gam, d, n):
    coeffs = []
    for j in range(d, -1, -1):  # leading first for mp.polyroots
        c = Fraction(mp.binomial(d, j).__int__() if False else 0)
        # exact binomial via python
        from math import comb
        c = Fraction(comb(d, j)) * gam(n + j)
        coeffs.append(mp.mpf(c.numerator) / mp.mpf(c.denominator))
    # strip leading zeros (gamma never 0 here, but guard)
    while coeffs and coeffs[0] == 0:
        coeffs = coeffs[1:]
    if len(coeffs) <= 1:
        return 0
    roots = mp.polyroots(coeffs, maxsteps=200, extraprec=200)
    nonreal = sum(1 for r in roots if abs(mp.im(r)) / (1 + abs(r)) > mp.mpf('1e-30'))
    assert nonreal % 2 == 0
    return nonreal // 2


def run(label, two_a, mod2):
    print(f"== {label}: P = x^2 - {two_a} x + {mod2} ==")
    gam = lambda m: gamma_quad_times_g(m, two_a, mod2)
    ds = [4, 6, 8, 10, 14, 20, 30, 40]
    ns = list(range(0, 25))
    print("d\\n " + " ".join(f"{n:2d}" for n in ns))
    worst = 0
    for d in ds:
        row = []
        for n in ns:
            c = pair_count(gam, d, n)
            worst = max(worst, c)
            row.append(c)
        print(f"d={d:2d} " + " ".join(f"{c:2d}" for c in row))
    print(f"max pair count = {worst}")
    return worst


if __name__ == "__main__":
    wc = run("CONTROL  F0 = (x-6)(x-14) cos(sqrt x)  [expect all 0]", 20, 84)
    ww = run("WITNESS  F  = (x-(10+4i))(x-(10-4i)) cos(sqrt x)  [expect {0,1}]", 20, 116)
    print()
    print(f"P1 (control all zero): {'PASS' if wc == 0 else 'FAIL'}")
    print(f"P2 (witness <= 1):     {'PASS' if ww <= 1 else 'FAIL'}")


def run_band_calibration():
    """Refinement (pre-registered AFTER run 1, BEFORE run 2): move the pair to
    higher zero-index; prediction P4: the count-1 region is a band of small n
    whose upper edge grows with the pair's zero-index, with a d-threshold that
    grows too (the section must be wide enough to reach the pair)."""
    for label, two_a, mod2 in [
        ("tau = 60+8i   (between zero #1 ~22.2 and #2 ~61.7, index ~2)", 120, 3664),
        ("tau = 120+10i (between zero #3 ~121.0 and #2 ~61.7, index ~3)", 240, 14500),
    ]:
        run(f"WITNESS {label}", two_a, mod2)


if __name__ == "__main__" and True:
    run_band_calibration()

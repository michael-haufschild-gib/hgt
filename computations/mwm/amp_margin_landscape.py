#!/usr/bin/env python3
"""
(AMP') margin landscape -- #135 (AMP) attack, doc 24.

At every critical point c of A_d = J^d_g:
  margin(c) := q_d(c) / (c^4 * E(c)),   E(c) = sum_k (c - alpha_k)^{-2},
  q_d(c) = |tau|^2 - 2 a d c + d(d-1) c^2.
Sign transfer at c  <=>  margin(c) > 1.  Z_c <= 2 + 2*#{margin <= 1}.

PRE-REGISTERED (before first run):
  PO: #failures = 0 (margin_min > 1) for all d >= 8 in model 1 (tau = 10+4i,
      q_d positive definite iff d > 1 + a^2/b^2 = 7.25 -- matches the measured
      visibility threshold d >= 10 in run 1) and for all d >= 4 in model 2
      (tau = 8i at the recentered-60 carrier, a = 0: q_d never dips).
  PP: margin_min(d) grows with d; report location of the minimizer (predict: the
      dip region c ~ a/(d-1) for model 1, the far/largest-c extrema for model 2).
  FALSIFIER: persistent margin <= 1 at extrema NOT adjacent to the detection
      region kills the F = 0 form; the theorem then needs the 2+2F bookkeeping.
"""
from fractions import Fraction
from math import comb
import mpmath as mp

mp.mp.dps = 60
KMAX = 200
MMAX = 42


def gamma_at0():
    fact2 = [Fraction(1)]
    for i in range(1, 2 * MMAX + 3):
        fact2.append(fact2[-1] * i)
    return [Fraction((-1) ** m) * fact2[m] / fact2[2 * m] for m in range(MMAX + 1)]


def gamma_at(x0):
    fact2 = [Fraction(1)]
    for i in range(1, 2 * KMAX + 1):
        fact2.append(fact2[-1] * i)
    gam, fm = [], Fraction(1)
    for m in range(MMAX + 1):
        s = Fraction(0)
        for k in range(m, KMAX + 1):
            s += Fraction((-1) ** k) * comb(k, m) * Fraction(x0) ** (k - m) / fact2[2 * k]
        gam.append(fm * s)
        fm *= (m + 1)
    return gam


def poly_coeffs(gam, d):
    return [mp.mpf((Fraction(comb(d, j)) * gam[j]).numerator) /
            mp.mpf((Fraction(comb(d, j)) * gam[j]).denominator) for j in range(d, -1, -1)]


def run(label, gam, a, b, ds):
    tau2 = mp.mpf(a) ** 2 + mp.mpf(b) ** 2
    print(f"== {label} (tau = {a}+{b}i) ==")
    print("d    #fail  margin_min    at c          note")
    for d in ds:
        A = poly_coeffs(gam, d)
        roots = mp.polyroots(A, maxsteps=300, extraprec=300)
        alph = sorted([mp.re(r) for r in roots])
        dA = [A[j] * (d - j) for j in range(d)]
        crits = mp.polyroots(dA, maxsteps=300, extraprec=300)
        crits = sorted([mp.re(r) for r in crits if abs(mp.im(r)) < mp.mpf('1e-30')])
        mmin, cmin, fails = mp.mpf('inf'), None, 0
        for c in crits:
            E = sum((c - al) ** -2 for al in alph)
            q = tau2 - 2 * a * d * c + d * (d - 1) * c * c
            marg = q / (c ** 4 * E) if c != 0 else mp.mpf('inf')
            if marg <= 1:
                fails += 1
            if marg < mmin:
                mmin, cmin = marg, c
        print(f"d={d:<3d} {fails:<6d} {mp.nstr(mmin, 6):<13s} {mp.nstr(cmin, 6):<13s}"
              f" {'ALL TRANSFER' if fails == 0 else 'FAILURES'}")


if __name__ == "__main__":
    run("model 1: g = cos(sqrt x) at 0", gamma_at0(), 10, 4, [6, 8, 10, 14, 20, 30, 40])
    run("model 2: recentered 60, pair +-8i", gamma_at(60), 0, 8, [4, 6, 8, 10, 14, 20, 30, 40])

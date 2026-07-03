#!/usr/bin/env python3
"""
(SPUR-crux) Hermite-Biehler chain probe -- task #135, doc 23.

PRE-REGISTERED PREDICTIONS (before first run):
  For g in LP, define the complex half-step H_m(x) = -tau*J^m_g(x) + m*x*J^{m-1}_g(x)
  (= the Jensen section of (.-tau)g, by the exact one-step recursion).
  PROVED on paper: if ALL zeros of the J^m_g chain are POSITIVE reals (one-sided,
  interlacing), then for tau in C^+ all zeros of H_m lie in the closed LOWER
  half-plane (Pick-function argument on W(x) = m x J^{m-1}/J^m).
  PG (one-sided validation): g = cos(sqrt(x)) at center 0, tau = 10+4i:
     max Im(zero of H_m) <= tol for m in 4..20.  [validates code + proof]
  PH (two-sided EXPERIMENT, prior 0.5): g = cos(sqrt(60+h)) recentered (real zeros
     of both signs), tau = 8i and tau = 3+8i:
     are all zeros of H_m in Im <= 0?  OPEN either way:
     YES -> the HB-Jensen route to (SPUR-crux) is live in full generality;
     NO  -> crux needs the real-combination route; record witness.
  PI (interlacing sanity): consecutive J^m_g interlace (polar-derivative theorem);
     checked numerically for both carriers.
"""
from fractions import Fraction
from math import comb
import mpmath as mp

mp.mp.dps = 60
KMAX = 200
MMAX = 40


def gamma_cos_sqrt_at0():
    g = []
    f = Fraction(1)
    fact2 = [Fraction(1)]
    for i in range(1, 2 * MMAX + 3):
        fact2.append(fact2[-1] * i)
    for m in range(MMAX + 1):
        g.append(Fraction((-1) ** m) * fact2[m] / fact2[2 * m])
    return g


def gamma_cos_sqrt_at(x0):
    fact2 = [Fraction(1)]
    for i in range(1, 2 * KMAX + 1):
        fact2.append(fact2[-1] * i)
    gam = []
    fm = Fraction(1)
    for m in range(MMAX + 1):
        s = Fraction(0)
        for k in range(m, KMAX + 1):
            s += Fraction((-1) ** k) * comb(k, m) * Fraction(x0) ** (k - m) / fact2[2 * k]
        gam.append(fm * s)
        fm *= (m + 1)
    return gam


def jensen(gam, d):
    return [mp.mpf((Fraction(comb(d, j)) * gam[j]).numerator) /
            mp.mpf((Fraction(comb(d, j)) * gam[j]).denominator) for j in range(d, -1, -1)]


def roots_of(coeffs):
    while coeffs and coeffs[0] == 0:
        coeffs = coeffs[1:]
    if len(coeffs) <= 1:
        return []
    return mp.polyroots(coeffs, maxsteps=300, extraprec=300)


def H_roots(gam, m, tau):
    A = jensen(gam, m)          # degree m, leading first
    B = jensen(gam, m - 1)      # degree m-1
    # H_m = -tau*A + m*x*B  -> degree m
    coeffs = [(-tau) * A[0] + m * B[0]]
    for j in range(1, m):
        coeffs.append((-tau) * A[j] + m * B[j])
    coeffs.append((-tau) * A[m])
    return roots_of(coeffs)


def probe(label, gam, taus):
    print(f"== {label} ==")
    # PI interlacing sanity for m=6..12
    ok = True
    for m in range(6, 13):
        ra = sorted([mp.re(r) for r in roots_of(jensen(gam, m))])
        rb = sorted([mp.re(r) for r in roots_of(jensen(gam, m - 1))])
        for i in range(len(rb)):
            if not (ra[i] <= rb[i] + mp.mpf('1e-30') and rb[i] <= ra[i + 1] + mp.mpf('1e-30')):
                ok = False
    print(f"PI interlacing m=6..12: {'PASS' if ok else 'FAIL'}")
    for tau in taus:
        worst = mp.mpf('-inf')
        for m in range(4, 21):
            for r in H_roots(gam, m, tau):
                worst = max(worst, mp.im(r))
        print(f"tau = {tau}:  max Im(zero of H_m, m=4..20) = {mp.nstr(worst, 6)}  "
              f"({'C^- stable' if worst < mp.mpf('1e-25') else 'UPPER-HALF ZEROS'})")


if __name__ == "__main__":
    probe("one-sided: g = cos(sqrt(x)) at 0 (positive zeros)",
          gamma_cos_sqrt_at0(), [mp.mpc(10, 4)])
    probe("two-sided: g = cos(sqrt(60+h)) recentered",
          gamma_cos_sqrt_at(60), [mp.mpc(0, 8), mp.mpc(3, 8)])

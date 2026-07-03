#!/usr/bin/env python3
"""
(SPUR-crux) half-plane COUNT probe -- task #135, doc 23. Follow-up to hb_chain_probe.

CORRECTION RECORDED: the half-step stability claim was FALSE (sign error: c_k*alpha_k < 0
in both one-sided orientations, so W is Pick and tau-points in C^+ exist). New target
invariant, PRE-REGISTERED (prior 0.6):
  PJ: Jensen sections are half-plane-count non-increasing:
      for h = (.-tau)g, g in LP (so h has exactly 1 upper zero, 0 lower, rest real),
      every section H_m = J^m_h has  #upper(H_m) <= 1 and #lower(H_m) = 0.
      Test: one-sided carrier (cos sqrt at 0), two-sided carrier (cos sqrt(60+.)),
      tau in {10+4i (near zeros), 3+8i, 8i (two-sided run)} as applicable, m = 4..24.
  PK: same with conjugate factor (.-taubar): #lower <= 1, #upper = 0.
  FALSIFIER: any m with #upper >= 2 (or nonzero #lower in PJ) kills the HB-Jensen
  route; then (SPUR-crux) needs the real-combination route.
"""
from fractions import Fraction
from math import comb
import mpmath as mp

mp.mp.dps = 60
KMAX = 200
MMAX = 26


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


def jensen_c(gam_c, d):
    return [mp.mpc(gam_c[j]) * comb(d, j) for j in range(d, -1, -1)]


def half_counts(gam, tau, m, conjugate=False):
    t = mp.conj(tau) if conjugate else tau
    # gamma of (.-t)g:  gam_h(j) = -t*gam(j) + j*gam(j-1)
    gh = []
    for j in range(m + 1):
        v = -t * (mp.mpf(gam[j].numerator) / mp.mpf(gam[j].denominator))
        if j >= 1:
            v += j * (mp.mpf(gam[j - 1].numerator) / mp.mpf(gam[j - 1].denominator))
        gh.append(v)
    coeffs = [gh[j] * comb(m, j) for j in range(m, -1, -1)]
    while coeffs and coeffs[0] == 0:
        coeffs = coeffs[1:]
    if len(coeffs) <= 1:
        return 0, 0
    roots = mp.polyroots(coeffs, maxsteps=300, extraprec=300)
    tol = mp.mpf('1e-30')
    up = sum(1 for r in roots if mp.im(r) / (1 + abs(r)) > tol)
    lo = sum(1 for r in roots if mp.im(r) / (1 + abs(r)) < -tol)
    return up, lo


def run(label, gam, taus):
    print(f"== {label} ==")
    allok_j = True
    allok_k = True
    for tau in taus:
        wu = wl = cu = cl = 0
        for m in range(4, MMAX - 1):
            u, l = half_counts(gam, tau, m)
            wu, wl = max(wu, u), max(wl, l)
            u2, l2 = half_counts(gam, tau, m, conjugate=True)
            cu, cl = max(cu, u2), max(cl, l2)
        print(f"tau={tau}: (.-tau)g sections max #upper={wu} #lower={wl} | "
              f"(.-taubar)g sections max #upper={cu} #lower={cl}")
        if wu > 1 or wl > 0:
            allok_j = False
        if cl > 1 or cu > 0:
            allok_k = False
    print(f"PJ {'PASS' if allok_j else 'FAIL'}   PK {'PASS' if allok_k else 'FAIL'}")


if __name__ == "__main__":
    run("one-sided: cos(sqrt x) at 0", gamma_at0(), [mp.mpc(10, 4)])
    run("two-sided: cos(sqrt(60+h))", gamma_at(60), [mp.mpc(0, 8), mp.mpc(3, 8)])

#!/usr/bin/env python3
"""
(AMP) crossing-structure probe -- follow-up to amp_margin_landscape (doc 24).

Corrected counting lemma: strict margin<1 FORCES sign flip (J(c) = q A + c^4 A'',
sign = sign(A'') = -sign(A)); flips alternate among themselves; so
  Z_c <= 2 + T,  T = #crossings of (margin - 1) along ordered critical points,
and T = 1 with evenness gives Z_c <= 2.

PRE-REGISTERED (before this run):
  PQ: T = 1 for model 1 (all d >= 8) and for model 2 on the positive side with
      T = 0 on the (short) negative side -- failure sets are one contiguous
      TOP block. (prior 0.7)
  PR: margin_i is decreasing along the ordered extrema in the outer half of the
      range (monotone approach to and through the crossing). (prior 0.6)
  FALSIFIER: multiple interleaved crossings (T >= 3 persistent) kills the
      single-crossing form; the theorem would need genuinely new bookkeeping.
"""
from fractions import Fraction
from math import comb
import mpmath as mp

mp.mp.dps = 60
KMAX = 200
MMAX = 42


def gamma_at0():
    f2 = [Fraction(1)]
    for i in range(1, 2 * MMAX + 3):
        f2.append(f2[-1] * i)
    return [Fraction((-1) ** m) * f2[m] / f2[2 * m] for m in range(MMAX + 1)]


def gamma_at(x0):
    f2 = [Fraction(1)]
    for i in range(1, 2 * KMAX + 1):
        f2.append(f2[-1] * i)
    gam, fm = [], Fraction(1)
    for m in range(MMAX + 1):
        s = Fraction(0)
        for k in range(m, KMAX + 1):
            s += Fraction((-1) ** k) * comb(k, m) * Fraction(x0) ** (k - m) / f2[2 * k]
        gam.append(fm * s)
        fm *= (m + 1)
    return gam


def margins(gam, a, b, d):
    tau2 = mp.mpf(a) ** 2 + mp.mpf(b) ** 2
    A = [mp.mpf((Fraction(comb(d, j)) * gam[j]).numerator) /
         mp.mpf((Fraction(comb(d, j)) * gam[j]).denominator) for j in range(d, -1, -1)]
    alph = sorted(mp.re(r) for r in mp.polyroots(A, maxsteps=300, extraprec=300))
    dA = [A[j] * (d - j) for j in range(d)]
    crits = sorted(mp.re(r) for r in mp.polyroots(dA, maxsteps=300, extraprec=300)
                   if abs(mp.im(r)) < mp.mpf('1e-30'))
    out = []
    for c in crits:
        E = sum((c - al) ** -2 for al in alph)
        q = tau2 - 2 * a * d * c + d * (d - 1) * c * c
        out.append((c, q / (c ** 4 * E)))
    return out


def analyze(label, gam, a, b, ds):
    print(f"== {label} ==")
    for d in ds:
        ms = margins(gam, a, b, d)
        seq = [(c, m) for c, m in ms]
        # crossings of margin-1 along ordered c
        signs = [1 if m > 1 else -1 for _, m in seq]
        T = sum(1 for i in range(len(signs) - 1) if signs[i] != signs[i + 1])
        # monotone-decrease violations in outer half (positive side)
        pos = [(c, m) for c, m in seq if c > 0]
        outer = pos[len(pos) // 2:]
        viol = sum(1 for i in range(len(outer) - 1) if outer[i + 1][1] > outer[i][1])
        neg = [(c, m) for c, m in seq if c < 0]
        Tneg = sum(1 for i in range(len(neg) - 1)
                   if (neg[i][1] > 1) != (neg[i + 1][1] > 1))
        print(f"d={d:<3d} #crit={len(seq):<3d} T_total={T} T_neg={Tneg} "
              f"outer-half monotone-violations={viol} "
              f"first-fail c={mp.nstr(next((c for c, m in seq if m <= 1), mp.mpf(0)), 5)}")


if __name__ == "__main__":
    analyze("model 1: at 0, tau=10+4i", gamma_at0(), 10, 4, [8, 10, 14, 20, 30, 40])
    analyze("model 2: recentered 60, tau=8i", gamma_at(60), 0, 8, [4, 6, 8, 10, 14, 20, 30, 40])

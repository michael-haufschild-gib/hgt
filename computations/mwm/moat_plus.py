#!/usr/bin/env python3
"""
Doc 43 SS9 route (3): Lemma MOAT+ (multi-zero, r-optimized) applied to the 8
mid-band survivors.

MOAT+ [proved, doc 44]: |Phi(s0)| <= eta^2 * prod_{j in S}[d_j/(r-d_j)]
  * M_r/(r-eta)^2, any r, any subset S of Phi-zeros in the disc; event killed
  (not self-dominated) iff this bound <= E*(t0) = |gamma(1/2+it0)|(t0/2pi)^{-1/4}
  (same declared E as the main classification).

Per survivor: scan on-line zeros of Z_g within +-1.7 of t0 (sign changes +
bisection); optimize margin over r in {0.5,0.75,1.0,1.25,1.5} and S = {zeros
with d_j < r/2}.

PRE-REGISTERED (before run):
  P-M1 (prior 0.60): >= 6 of 8 survivors get margin <= 1 (lemma-killed).
  P-M2 (prior 0.35): all 8 killed (measured wall at accessible heights = 0).
  P-M3 (prior 0.70): the TRUE error |zeta - g_N|(1/2+it0) is <= the declared
       E(t0) = (t0/2pi)^{-1/4} at all 8 points (validates the declared bound
       where the lemma uses it; measured with mpmath RS zeta).
"""
from mpmath import (mp, mpc, mpf, pi, sqrt, findroot, re, im, fabs,
                    gamma as Gamma, exp, zeta)
from euler_suppression_boxcount import make_phi, coeffs

mp.dps = 40
NC = 50
SURV = [(mpf('1415.6767'), 14, mpf('0.17106')),
        (mpf('4253.5428'), 26, mpf('0.11541')),
        (mpf('4589.7089'), 27, mpf('0.17795')),
        (mpf('4990.3903'), 28, mpf('0.14232')),
        (mpf('6430.8007'), 31, mpf('0.11566')),
        (mpf('7712.8523'), 35, mpf('0.09619')),
        (mpf('7734.7144'), 35, mpf('0.09711')),
        (mpf('11127.6330'), 42, mpf('0.12190'))]

a = coeffs('E', 0, NC)

def online_zeros(phi, t0, halfw):
    Z = lambda t: re(phi(mpc(mpf('0.5'), t)))
    ts = [t0 - halfw + mpf('0.04') * k for k in range(int(2 * halfw / 0.04) + 1)]
    vals = [Z(t) for t in ts]
    zs = []
    for i in range(len(ts) - 1):
        if vals[i] * vals[i + 1] < 0:
            lo, hi = ts[i], ts[i + 1]
            for _ in range(40):
                mid = (lo + hi) / 2
                if Z(lo) * Z(mid) <= 0:
                    hi = mid
                else:
                    lo = mid
            zs.append((lo + hi) / 2)
    return zs

killed = 0
true_err_ok = 0
for t0, N, eta in SURV:
    phi = make_phi(a, N)
    s0 = mpc(mpf('0.5'), t0)
    Estar = fabs(pi ** (-s0 / 2) * Gamma(s0 / 2)) * (t0 / (2 * pi)) ** mpf('-0.25')
    zs = online_zeros(phi, t0, mpf('1.7'))
    best, bestr, bestS = None, None, 0
    for rr in ('0.5', '0.75', '1.0', '1.25', '1.5'):
        r = mpf(rr)
        Mr = max(fabs(phi(s0 + r * exp(mpc(0, 2 * pi * k / 96))))
                 for k in range(96))
        prod = mpf(1)
        nS = 0
        for g in zs:
            d = fabs(g - t0)
            if d < r / 2:
                prod *= d / (r - d)
                nS += 1
        margin = eta ** 2 * prod * Mr / ((r - eta) ** 2 * Estar)
        if best is None or margin < best:
            best, bestr, bestS = margin, rr, nS
    # true-error check at s0 (uncompleted normalization: ratio-free comparison)
    gN = sum(mpf(n) ** (-s0) for n in range(1, N + 1))
    chi_gN = phi(s0) / (pi ** (-s0 / 2) * Gamma(s0 / 2)) - gN  # chi(s0)*A(1-s0)
    terr = fabs(zeta(s0) - (gN + chi_gN))
    Edecl = (t0 / (2 * pi)) ** mpf('-0.25')
    ok = terr <= Edecl
    true_err_ok += 1 if ok else 0
    kill = best <= 1
    killed += 1 if kill else 0
    print(f"t0={float(t0):.1f}: nZ={len(zs)} bestS={bestS} r={bestr} "
          f"margin={float(best):.3f} {'KILLED' if kill else 'SURVIVES'} | "
          f"true err={float(terr):.4f} vs E={float(Edecl):.4f} "
          f"{'OK' if ok else 'EXCEEDS'}")

print(f"\nP-M1 killed {killed}/8: {'PASS' if killed >= 6 else 'FAIL'}")
print(f"P-M2 all killed: {'PASS' if killed == 8 else 'FAIL'}")
print(f"P-M3 true error <= declared at {true_err_ok}/8: "
      f"{'PASS' if true_err_ok == 8 else 'FAIL'}")

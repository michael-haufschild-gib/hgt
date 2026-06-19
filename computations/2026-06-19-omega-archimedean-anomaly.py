#!/usr/bin/env python3
"""
compute-omega-h2-gl §S pre-certification (Professor, 2026-06-19).

Goal: certify the operator-language face of D4 Layer-1 — the archimedean
multiplicative anomaly of the zeta-regularized determinant is a NONZERO,
computable constant (the Lerch / Hurwitz counterterm = 1/2 log 2pi),
confirming "substrate-with-content" (omega != 0 at the symmetry level).

Identity tested (zeta-regularized determinant of the shift operator):
    det_zeta(shift_a) := exp(-d/dz zeta_H(z,a) |_{z=0})  ==  sqrt(2pi)/Gamma(a).
The sqrt(2pi) = exp(1/2 log 2pi) is the multiplicative anomaly the
regularization injects: the NAIVE product prod_{n>=0}(n+a) carries no 2pi,
the zeta-regularized one does. That injected archimedean constant is omega's
Layer-1 value. Nonzero => weld does not factor trivially (cf. #132 [chi]!=1).

Fast: a handful of mpmath evaluations, no loops over primes.
"""
import mpmath as mp
mp.mp.dps = 40

half_log_2pi = mp.mpf('0.5') * mp.log(2*mp.pi)

def zeta_det_shift(a):
    # det_zeta(shift_a) = exp(-zeta_H'(0,a)), derivative in the FIRST argument
    dz = mp.diff(lambda z: mp.zeta(z, a), 0)   # d/dz zeta(z,a) at z=0
    return mp.e**(-dz)

print("half_log_2pi          =", half_log_2pi)
print()
for a in ['1', '2', '3', '0.5', '1.5', '2.7']:
    av = mp.mpf(a)
    lhs = zeta_det_shift(av)
    rhs = mp.sqrt(2*mp.pi) / mp.gamma(av)
    print(f"a={a:>4}:  det_zeta(shift_a) = {mp.nstr(lhs,25)}")
    print(f"        sqrt(2pi)/Gamma(a) = {mp.nstr(rhs,25)}   |diff| = {mp.nstr(abs(lhs-rhs),5)}")

# Lerch form: zeta_H'(0,a) = log Gamma(a) - 1/2 log 2pi  (the counterterm is -1/2 log 2pi)
print()
print("Lerch check  zeta_H'(0,a) vs  logGamma(a) - 1/2 log 2pi:")
for a in ['1', '2', '3.3']:
    av = mp.mpf(a)
    lhs = mp.diff(lambda z: mp.zeta(z, av), 0)
    rhs = mp.loggamma(av) - half_log_2pi
    print(f"  a={a:>4}:  {mp.nstr(lhs,25)}  vs  {mp.nstr(rhs,25)}   |diff|={mp.nstr(abs(lhs-rhs),5)}")

# The anomaly is NONZERO and place-localized to infinity:
print()
print("ANOMALY CONSTANT (Layer-1 omega, archimedean) = 1/2 log 2pi =",
      mp.nstr(half_log_2pi, 30), "!= 0")

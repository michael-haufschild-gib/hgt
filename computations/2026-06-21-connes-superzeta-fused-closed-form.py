#!/usr/bin/env python3
"""
connes 2026-06-21 — CERTIFY the fused closed form (one formula from 3 corpus formulas).

Claim (derived by mangling weld + Hadamard/superzeta + Gamma-completion identities):

  S_k := sum_rho (rho-1/2)^{-2k}
       =  2^{2k}  -  (1/4)(2^{2k}-1) zeta(2k)  -  2^{2k-2} beta(2k)        [ = S_k^A, archimedean ]
          -  (1/(2*(2k-1)!)) * (zeta'/zeta)^{(2k-1)}(1/2)                   [ = S_k^P, prime ]

where beta = Dirichlet beta (beta(2)=Catalan G).  Used:
  psi^{(2k-1)}(1/4) = (2k-1)! * zeta(2k, 1/4)  (Hurwitz),
  zeta(2k,1/4) = (1/2)[(4^{2k}-2^{2k}) zeta(2k) + 4^{2k} beta(2k)].

This script checks the ARCHIMEDEAN closed form S_k^A against the Taylor coefficient of A(1/2+w),
and the FULL fused S_k against S_k from log Xi.  Local, seconds.
"""
import mpmath as mp

mp.mp.dps = 40
half = mp.mpf(1) / 2
K = 6

def A_half(w):
    s = half + w
    return 1/s + 1/(s - 1) - half*mp.log(mp.pi) + half*mp.digamma(s/2)

def P_half(w):
    s = half + w
    return mp.zeta(s, 1, 1) / mp.zeta(s)

def logXi(w):
    s = half + w
    return mp.log(half * s * (s - 1) * mp.power(mp.pi, -s/2) * mp.gamma(s/2) * mp.zeta(s))

cA = mp.taylor(A_half, 0, 2*K + 1)
cP = mp.taylor(P_half, 0, 2*K + 1)
cL = mp.taylor(logXi, 0, 2*K + 2)

def beta(s):                       # Dirichlet beta via Hurwitz: 4^-s (zeta(s,1/4)-zeta(s,3/4))
    return mp.power(4, -s) * (mp.zeta(s, mp.mpf(1)/4) - mp.zeta(s, mp.mpf(3)/4))

print(f"[setup] dps={mp.mp.dps}  K={K}")
print(" k |   S_k^A closed form   | S_k^A Taylor          | match    | full S_k fused vs logXi")
for k in range(1, K+1):
    z2k = mp.zeta(2*k)
    b2k = beta(2*k)
    SkA_closed = 2**(2*k) - mp.mpf(1)/4*(2**(2*k) - 1)*z2k - 2**(2*k - 2)*b2k
    SkA_taylor = -half * cA[2*k - 1]
    SkP_taylor = -half * cP[2*k - 1]
    Sk_logxi   = -mp.mpf(k) * cL[2*k]
    full_fused = SkA_closed + SkP_taylor          # closed arch + (computed) prime
    mA = abs(SkA_closed - SkA_taylor)
    mfull = abs(full_fused - Sk_logxi)
    print(f" {k} | {mp.nstr(SkA_closed,14):>20} | {mp.nstr(SkA_taylor,14):>20} |"
          f" {mp.nstr(mA,3):>8} | S_k={mp.nstr(Sk_logxi,8)}  |fused-logXi|={mp.nstr(mfull,3)}")

print()
print("If S_k^A closed == Taylor (match ~1e-38) for all k: the fused archimedean closed form is")
print("CERTIFIED. The full identity then reads S_k = S_k^A(closed) + S_k^P, prime = -(zeta'/zeta)")
print("derivative at 1/2 -- one formula fusing zeros = (pi-periods + Catalan beta) + primes.")

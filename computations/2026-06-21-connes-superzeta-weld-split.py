#!/usr/bin/env python3
"""
connes 2026-06-21 — CONNECT note-12 superzeta values to the weld H=A+P (and the phase defect).

Connecting transform (standard, no new machinery):
  Xi'/Xi(w) = xi'/xi(1/2+w) = A(1/2+w) + P(1/2+w),
    A(s) = 1/s + 1/(s-1) - 1/2 log pi + 1/2 psi(s/2)     [archimedean weld half]
    P(s) = zeta'/zeta(s)                                  [prime weld half]
  and (note 12)  Xi'/Xi(w) = -2 sum_{k>=1} S_k w^{2k-1},  S_k = sum_rho (rho-1/2)^{-2k}.
Therefore every superzeta value splits along the weld:
  S_k = S_k^A + S_k^P,   S_k^{A/P} = -1/2 * [w^{2k-1}] (A/P)(1/2+w).
On RH, T_k := (-1)^k S_k = sum_{gamma>0} 1/gamma^{2k} > 0.  Question this script answers:
  which weld half CARRIES the positivity?  i.e. compare T_k^A := (-1)^k S_k^A  vs  T_k^P.
This connects three corpus boxes: superzeta {S_k}  <->  weld A+P  <->  phase-carrier A-vs-P balance.
Checks: (i) S_k^A+S_k^P == S_k (direct from logXi); (ii) signs and A/P shares.
"""
import mpmath as mp

mp.mp.dps = 40
half = mp.mpf(1) / 2
K = 8

def A_half(w):           # archimedean weld half at s = 1/2 + w
    s = half + w
    return 1/s + 1/(s - 1) - half*mp.log(mp.pi) + half*mp.digamma(s/2)

def P_half(w):           # prime weld half  zeta'/zeta at s = 1/2 + w
    s = half + w
    return mp.zeta(s, 1, 1) / mp.zeta(s)

def logXi(w):
    s = half + w
    return mp.log(half * s * (s - 1) * mp.power(mp.pi, -s/2) * mp.gamma(s/2) * mp.zeta(s))

# Taylor coefficients
cA = mp.taylor(A_half, 0, 2*K + 1)
cP = mp.taylor(P_half, 0, 2*K + 1)
cL = mp.taylor(logXi, 0, 2*K + 2)        # log Xi: S_k = -k*[w^2k]

print(f"[setup] dps={mp.mp.dps}  K={K}")
print(f"[const] A even part at seam: -1/2 log pi + 1/2 psi(1/4) = {mp.nstr(cA[0],12)}")
print()
print(" k |        S_k (direct)        S_k^A (arch)        S_k^P (prime)   |  A+P check  | |S^P|/|S^A| | T_k^A sign")
for k in range(1, K+1):
    Sk_direct = -mp.mpf(k) * cL[2*k]
    SkA = -half * cA[2*k - 1]
    SkP = -half * cP[2*k - 1]
    check = abs((SkA + SkP) - Sk_direct)
    TkA = ((-1)**k) * SkA
    TkP = ((-1)**k) * SkP
    ratio = abs(SkP) / abs(SkA)
    print(f" {k} | {mp.nstr(Sk_direct,11):>17} {mp.nstr(SkA,11):>17} {mp.nstr(SkP,11):>17} |"
          f" {mp.nstr(check,3):>9} | {mp.nstr(ratio,6):>9} |"
          f" T^A={mp.nstr(TkA,8)} T^P={mp.nstr(TkP,8)}")

# magnitude law: halves ~ 2^{2k-1} (s=1 pole, dist 1/2);  residue S_k ~ gamma_1^{-2k} (first zero)
g1 = mp.im(mp.zetazero(1))
print()
print(" k | |S_k^A| ~ 2^{2k-1}? | |S_k| vs gamma_1^{-2k} | agreement depth |S_k|/|S_k^A|")
for k in range(1, K+1):
    cL = mp.taylor(logXi, 0, 2*K + 2)
    Sk = -mp.mpf(k) * cL[2*k]
    SkA = -half * cA[2*k - 1]
    print(f" {k} | |S^A|={mp.nstr(abs(SkA),7):>11}  2^(2k-1)={2**(2*k-1):>6} |"
          f" |S_k|={mp.nstr(abs(Sk),4):>10}  g1^-2k={mp.nstr(g1**(-2*k),4):>10} |"
          f" {mp.nstr(abs(Sk)/abs(SkA),4)}")
print()
print("READING (corrected):")
print(" - S_k = S_k^A + S_k^P exactly. The two weld halves are CO-DOMINANT and nearly cancel:")
print("   |S_k^A| ~ |S_k^P| ~ 2^{2k-1} (grows; scale = s=1 pole at distance 1/2 from seam),")
print("   while the true S_k ~ gamma_1^{-2k} (decays; scale = first zero). Agreement ~800^{-k}.")
print(" - Cause: A has +1/(s-1) (completion factor), P=zeta'/zeta has -1/(s-1) (zeta pole);")
print("   they cancel -> xi entire. Propagated to all Taylor orders at the seam.")
print(" - CONNECTS: phase-carrier defect (A<->P cancellation) = weld(A+P) = superzeta {S_k}")
print("   = entire-ness constraint. The RH-relevant values live in the residue of this cancellation.")

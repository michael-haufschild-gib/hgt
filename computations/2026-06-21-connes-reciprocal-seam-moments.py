#!/usr/bin/env python3
"""
connes 2026-06-21 — verify the reciprocal-seam-moment identity chain (revision01/12).

Claim chain to verify (all standard algebra, built out from corpus formulas):

  Xi(w) := xi(1/2 + w)  is EVEN entire, zeros w_rho = rho - 1/2.
  (1) log Xi(w) = log Xi(0) - sum_{k>=1} (S_k / k) w^{2k},
      where  S_k := sum over +/- pairs  (rho - 1/2)^{-2k}      [seam-centered reciprocal power sums]
      i.e.   S_k = -k * [w^{2k}] log Xi(w).
  (2) On RH, rho-1/2 = i*gamma, so (rho-1/2)^{-2k} = (-1)^k gamma^{-2k};
      define T_k := (-1)^k S_k  ==> on RH  T_k = sum_{gamma>0} gamma^{-2k} > 0.
  (3) RH  <=>  all w_rho^2 real-negative  <=>  {T_k}_{k>=1} is a Stieltjes moment
      sequence of the atomic measure sum_n delta_{y_n}, y_n = 1/gamma_n^2 > 0
      <=>  Hankel [T_{i+j}] and [T_{i+j+1}] (i,j>=1) are PSD.
  NB every S_k, T_k converges ABSOLUTELY from k=1 (|w_rho|^{-2} summable) -- this is the
  point: no regularization is needed once you pass to reciprocal seam-squared coordinates.

Checks:
  A. cross-check S_1 from Taylor of log Xi   vs   -sum_{gamma>0} 1/gamma^2 over first N zeros.
  B. T_k > 0 for k=1..K (RH-consistent positivity).
  C. Hankel [T_{i+j}]_{i,j=1..d} PSD (min eigenvalue >= 0) for d up to ~5  (necessary for RH).
Fast: Taylor to order 2K, a few hundred zeros for the cross-check. Minutes, chunked.
"""
import mpmath as mp

mp.mp.dps = 40
half = mp.mpf(1) / 2

def Xi(w):
    s = half + w
    return half * s * (s - 1) * mp.power(mp.pi, -s/2) * mp.gamma(s/2) * mp.zeta(s)

K = 12                       # number of reciprocal moments S_1..S_K
print(f"[setup] dps={mp.mp.dps}  K={K}")

# --- Taylor coefficients of log Xi at 0 (even function) ---
logXi = lambda w: mp.log(Xi(w))
# Xi(0) = xi(1/2) > 0, real; log well-defined near 0
c = mp.taylor(logXi, 0, 2*K + 2)        # c[n] = [w^n] log Xi
# S_k = -k * c[2k]
S = [None] + [ -mp.mpf(k) * c[2*k] for k in range(1, K+1) ]
T = [None] + [ ((-1)**k) * S[k] for k in range(1, K+1) ]

print("\n[A] S_k (seam-centered reciprocal power sums, = -k*[w^2k]logXi):")
for k in range(1, min(K,6)+1):
    print(f"   S_{k} = {mp.nstr(S[k], 12):>22}    T_{k}=(-1)^k S_k = {mp.nstr(T[k], 12):>20}")

# --- cross-check S_1 against sum over zeros: S_1 = -sum_{gamma>0} 1/gamma^2 ---
N = 300
acc = mp.mpf(0)
for n in range(1, N+1):
    g = mp.im(mp.zetazero(n))
    acc += 1/g**2
S1_zeros = -acc
print("\n[A-cross] S_1 from Taylor   =", mp.nstr(S[1], 15))
print("          -sum 1/gamma^2 (N=%d zeros) =" % N, mp.nstr(S1_zeros, 15))
print("          abs diff (tail ~ +/- sum_{n>N}1/g^2, small) =",
      mp.nstr(abs(S[1]-S1_zeros), 6))

# --- T_k positivity ---
allpos = all(mp.re(T[k]) > 0 and abs(mp.im(T[k])) < mp.mpf(10)**(-20) for k in range(1, K+1))
print("\n[B] all T_k real-positive (k=1..%d): %s" % (K, allpos))

# --- Hankel PSD of {T_k}: H^(0)=[T_{i+j}], H^(1)=[T_{i+j+1}], i,j=1..d ---
import numpy as np
def hankel(shift, d):
    return [[float(mp.re(T[i+j+shift])) for j in range(1, d+1)] for i in range(1, d+1)]
print("\n[C] Hankel min-eigenvalues (PSD necessary for RH):")
for d in range(1, K//2):
    if 2*d + 1 > K:
        break
    H0 = np.array(hankel(0, d)); H1 = np.array(hankel(1, d))
    e0 = float(np.linalg.eigvalsh(H0).min())
    e1 = float(np.linalg.eigvalsh(H1).min())
    print(f"   d={d}:  min eig H^(0)={e0:.3e}   min eig H^(1)={e1:.3e}   PSD={e0>=-1e-12 and e1>=-1e-12}")

# --- explicit first Turan/CS inequality: T_1 T_3 >= T_2^2 (auto by Cauchy-Schwarz on y_n>0) ---
lhs = mp.re(T[1]*T[3]); rhs = mp.re(T[2]**2)
print("\n[C-first] T_1*T_3 - T_2^2 =", mp.nstr(lhs - rhs, 8), " (>=0 expected, CS on y_n=1/gamma^2)")
print("\n[done]")

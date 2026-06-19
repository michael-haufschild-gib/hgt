#!/usr/bin/env python3
"""
Relative no-margin probe for the finite-free / Jensen carrier (Wheeler, 2026-06-19).

Tests the SCALE-INVARIANT criterion from finite-free-convolution-flow.md:
    H_d(t) = A_d + dH_d(t),   S_d(t) = A_d^{-1/2} dH_d(t) A_d^{-1/2},
    RH  <=>  lambda_min(S_d(t)) >= -1  for all d, t.
Sufficient clean form: rho_d(t) := ||S_d(t)||_op < 1.

Normalization-free construction (no kernel guess):
  - J_d(X;t) = sum_{j=0}^d C(d,j) Xi^{(j)}(t)/j! X^j   (Jensen poly of Xi at base point t)
  - H_d(t) = Hankel of power sums of J_d's roots (via Newton's identities -- stable)
  - A_d := mean_t H_d(t)        (archimedean / mean part; dH_d is mean-zero by Weyl)
  - dH_d(t) := H_d(t) - A_d
  - rho_d(t) := ||A_d^{-1/2} dH_d(t) A_d^{-1/2}||_op ,  mu_d(t):=lambda_min(A_d^{-1/2}H_d(t)A_d^{-1/2})-?
    we report lambda_min(I+S_d) = lambda_min(A_d^{-1/2} H_d(t) A_d^{-1/2})  (>=0  iff hyperbolic).

Question: does sup_t rho_d stay < 1, or approach 1 (no-margin) as d grows?
          does min_t lambda_min(I+S_d) stay > 0 (local hyperbolicity holds, as it must under RH)?

Bounded: d in 2..DMAX, t-grid NT points over [T0,T1]. Xi derivatives via Cauchy-integral diff.
"""
import mpmath as mp

mp.mp.dps = 100         # working precision (high: certify lambda_min sign for d>=5, cond up to ~1e60)
DMAX = 7                # max Jensen degree
T0, T1, NT = 0.5, 60.0, 61   # base-point grid; start off the symmetry point t=0 (Xi even -> c_d=0 there)
CD_GUARD = mp.mpf('1e-40')   # skip t where leading Jensen coeff is ~0 (near-degenerate)

def xi(s):
    # Riemann xi(s) = 1/2 s(s-1) pi^{-s/2} Gamma(s/2) zeta(s)
    return mp.mpf('0.5') * s * (s - 1) * mp.power(mp.pi, -s/2) * mp.gamma(s/2) * mp.zeta(s)

def Xi(z):
    # Xi(z) = xi(1/2 + i z); real for real z
    return xi(mp.mpf('0.5') + 1j*z)

def xi_derivs(t, n):
    # Xi^{(j)}(t)/j!  for j=0..n  (Taylor coefficients at real base point t)
    # mpmath taylor uses high-precision; force real part (Xi real on R).
    coeffs = mp.taylor(Xi, mp.mpf(t), n)   # returns [Xi^{(j)}(t)/j! for j=0..n]
    return [mp.re(c) for c in coeffs]

def jensen_coeffs(t, d):
    # c_j = C(d,j) * Xi^{(j)}(t)/j! ;  taylor already gives Xi^{(j)}/j!
    tc = xi_derivs(t, d)
    return [mp.binomial(d, j) * tc[j] for j in range(d+1)]

def power_sums_from_coeffs(c, d):
    # c[j] = coeff of X^j, j=0..d (c[d] leading). Monic-normalize, Newton's identities.
    cd = c[d]
    a = [c[j]/cd for j in range(d+1)]          # monic: prod (X - rho), sum a_j X^j, a_d=1
    # elementary symmetric e_k = (-1)^k * a_{d-k}
    e = [ (-1)**k * a[d-k] for k in range(d+1) ]   # e[0]=1
    p = [mp.mpf(d)]                              # p_0 = d
    # Newton: for k>=1, p_k = sum_{i=1}^{k-1} (-1)^{i-1} e_i p_{k-i} + (-1)^{k-1} k e_k   (k<=d)
    #         for k>d : p_k = sum_{i=1}^{d} (-1)^{i-1} e_i p_{k-i}
    for k in range(1, 2*d-1):
        s = mp.mpf(0)
        kk = min(k, d)
        for i in range(1, kk):
            s += (-1)**(i-1) * e[i] * p[k-i]
        if k <= d:
            s += (-1)**(k-1) * k * e[k]
        else:
            s += (-1)**(d-1) * e[d] * p[k-d]
        p.append(s)
    return p   # p[0..2d-2]

def hankel(p, d):
    return mp.matrix([[p[i+j] for j in range(d)] for i in range(d)])

def sym_eig(M, d):
    # symmetric real eigenvalues, sorted
    Msym = mp.matrix([[ (M[i,j]+M[j,i])/2 for j in range(d)] for i in range(d)])
    E = mp.eigsy(Msym, eigvals_only=True)
    return sorted([mp.re(x) for x in E])

def inv_sqrt(A, d):
    Asym = mp.matrix([[ (A[i,j]+A[j,i])/2 for j in range(d)] for i in range(d)])
    E, Q = mp.eigsy(Asym)
    # A^{-1/2} = Q diag(1/sqrt(lam)) Q^T
    Dm = mp.matrix(d, d)
    for i in range(d):
        Dm[i,i] = 1/mp.sqrt(E[i])
    return Q * Dm * Q.T

tgrid = [T0 + (T1-T0)*k/(NT-1) for k in range(NT)]

print(f"# relative rho probe  dps={mp.mp.dps} DMAX={DMAX} t in [{T0},{T1}] NT={NT}")
for d in range(2, DMAX+1):
    Hs = []; tused = []
    for t in tgrid:
        c = jensen_coeffs(t, d)
        if abs(c[d]) < CD_GUARD * (abs(c[0]) + 1):
            continue   # leading coeff ~0: degenerate Jensen poly at this t, skip
        p = power_sums_from_coeffs(c, d)
        Hs.append(hankel(p, d)); tused.append(t)
    # A_d = mean over t
    A = mp.matrix(d, d)
    for H in Hs:
        A += H
    A = A / len(Hs)
    try:
        Aih = inv_sqrt(A, d)
    except Exception as ex:
        print(f"d={d}: A_d not PD ({ex}); eig(A)={sym_eig(A,d)}")
        continue
    rho_max = mp.mpf(0); lam_min_global = mp.mpf('1e9'); t_at_min = None
    for t, H in zip(tused, Hs):
        S = Aih * (H - A) * Aih
        IpS = Aih * H * Aih               # = I + S
        es = sym_eig(S, d)
        rho = max(abs(es[0]), abs(es[-1]))
        if rho > rho_max: rho_max = rho
        lm = sym_eig(IpS, d)[0]
        if lm < lam_min_global:
            lam_min_global = lm; t_at_min = t
    eigA = sym_eig(A, d)
    condA = eigA[-1]/eigA[0]
    print(f"d={d}: sup_t rho_d={mp.nstr(rho_max,6)}  min_t lam_min(I+S)={mp.nstr(lam_min_global,6)} "
          f"@t={mp.nstr(t_at_min,5)}  cond(A_d)={mp.nstr(condA,4)}")
print("# done")

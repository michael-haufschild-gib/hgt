#!/usr/bin/env python3
"""Constrained archimedean Weil form on V0 as a Fourier multiplier (hgtl7 round, P2).
 On V0 = {f in L^2[-a,a] : int e^{+-x/2} f = 0}, S = 2a, the archimedean Weil form is
   Q(f) = A(S)|f|^2 + int_0^S D(u) K+(u) du,   D(u) = |f - T_u f|^2/2,  K+(u) = 2 e^{-u/2}/(1-e^{-2u}),
   A(S) = -gamma - log pi - log(1-e^{-2S}) - J(S),  J(S) = 2 int_0^S (e^{-u/2}-e^{-2u})/(1-e^{-2u}) du.
 Fourier side: Q(f) = (1/2pi) int |fhat|^2 m_S(xi) dxi, m_S = A(S) + Lambda_S(xi),
   Lambda_S(xi) = int_0^S 2 sin^2(u xi/2) K+(u) du.
 Checks: (1) m_S(xi) vs Re psi(1/4 + i xi/2) - log pi (the classical multiplier) for S -> infinity limit sanity;
 (2) constrained ground energy in the Legendre basis on [-a,a] (Gram of Q via the multiplier), N=48;
 (3) the negative band [-xi_S, xi_S], the concentration of the minimizer in it, prolate-type eigenvalues
     of the band-limiting operator restricted to V0-orthogonal directions; (4) Legendre tail decay."""
import numpy as np, math
from scipy import integrate, special
from numpy.polynomial import legendre as L
gam = 0.5772156649015329
def Kp(u): return 2*math.exp(-u/2)/(1-math.exp(-2*u))
def J(S): return 2*integrate.quad(lambda u: (math.exp(-u/2)-math.exp(-2*u))/(1-math.exp(-2*u)), 0, S)[0]
def A(S): return -gam - math.log(math.pi) - math.log(1-math.exp(-2*S)) - J(S)
def Lam(S, xi):
    return integrate.quad(lambda u: 2*math.sin(u*xi/2)**2*Kp(u), 0, S, limit=200)[0]
def m(S, xi): return A(S) + Lam(S, xi)
def classical(xi):  # Re psi(1/4 + i xi/2) - log pi
    return special.digamma(0.25 + 0.5j*xi).real - math.log(math.pi)
print("A(S):", [(S, round(A(S),4)) for S in (0.2, 0.5, math.log(2), 1.0, 1.19, 1.5)])
print("multiplier at S=log2 vs classical (should agree only as S->inf; difference is the support cutoff):")
for xi in (0, 1, 2, 4, 6, 8, 12, 20):
    print("  xi=%5.1f  m_S=%8.4f  classical=%8.4f" % (xi, m(math.log(2), xi), classical(xi)))
def xi_zero(S):
    lo, hi = 0.0, 100.0
    for _ in range(60):
        mid = (lo+hi)/2
        if m(S, mid) < 0: lo = mid
        else: hi = mid
    return hi
# Legendre-basis Gram of Q on [-a,a]: fhat_n(xi) for normalized Legendre p_n(x/a): 
# p_n(x/a) has Fourier transform (2a) (-i)^n j_n(a xi) * sqrt((2n+1)/(2a)) normalization
def gram(S, N, xi_max=400.0):
    a = S/2
    # quadrature in xi: fine grid, m(S,xi) sampled; use symmetric integrand
    xs = np.linspace(0, xi_max, 8001)
    ms = np.array([m(S, x) for x in xs])
    jn = np.array([special.spherical_jn(n, a*xs) for n in range(N)])
    # (1/2pi) int |fhat|^2 m = sum_{n,k} c_n c_k G_nk ; fhat = sum c_n sqrt((2n+1)/(2a)) 2a (-i)^n j_n(a xi)
    G = np.zeros((N, N))
    w = np.ones_like(xs); w[0] = w[-1] = 0.5; w *= (xs[1]-xs[0])
    for n in range(N):
        for k in range(n, N):
            if (n - k) % 2: continue
            phase = (-1)**((n - k)//2)  # (-i)^n (i)^k = i^{k-n}; real part for even k-n
            val = (2/(2*math.pi)) * np.sum(w * ms * jn[n] * jn[k]) * (2*a)**2 * math.sqrt((2*n+1)*(2*k+1))/(2*a) * phase
            G[n, k] = G[k, n] = val
    return G
def constraints(S, N):
    a = S/2
    # <e^{x/2}, p_n> and <e^{-x/2}, p_n> with normalized Legendre p_n(x) = sqrt((2n+1)/(2a)) P_n(x/a)
    C = np.zeros((2, N))
    for n in range(N):
        f = lambda x: math.sqrt((2*n+1)/(2*a)) * special.eval_legendre(n, x/a)
        C[0, n] = integrate.quad(lambda x: math.exp(x/2)*f(x), -a, a)[0]
        C[1, n] = integrate.quad(lambda x: math.exp(-x/2)*f(x), -a, a)[0]
    return C
def constrained_min(S, N):
    G = gram(S, N); C = constraints(S, N)
    # basis of the nullspace of C
    u, s, vt = np.linalg.svd(C)
    B = vt[2:].T
    Gc = B.T @ G @ B
    ev, V = np.linalg.eigh(Gc)
    return ev, B @ V[:, 0], G
for S in (0.5, math.log(2), 0.9, 1.0, 1.1, 1.19, 1.3):
    ev, v, G = constrained_min(S, 40)
    evfull = np.linalg.eigvalsh(G)
    print("S=%.4f  A=%.4f  xi_S=%.3f  c=a*xi_S=%.3f  constrained min=%.5f (2nd %.4f)  unconstrained min=%.5f" % (S, A(S), xi_zero(S), S/2*xi_zero(S), ev[0], ev[1], evfull[0]))
S = math.log(2); ev, v, G = constrained_min(S, 40)
print("minimizer Legendre coefficients (S=log2):", np.round(v[:10], 4))
a = S/2; xi0 = xi_zero(S)
xs = np.linspace(0, 60, 6001); w = np.ones_like(xs); w[0]=w[-1]=0.5; w *= xs[1]-xs[0]
fh = sum(v[n]*math.sqrt((2*n+1)/(2*a))*(2*a)*((-1j)**n)*special.spherical_jn(n, a*xs) for n in range(len(v)))
dens = np.abs(fh)**2/(2*math.pi)*2
print("minimizer: total spectral mass (should be 1):", np.sum(w*dens), " mass in negative band |xi|<%.2f: %.4f" % (xi0, np.sum(w*dens*(xs<xi0))))
# prolate-type concentration in the band for V0-constrained functions: max of <f, B f> with B = band-limit to |xi|<xi0
Bm = np.zeros((40, 40))
for n in range(40):
    for k in range(n, 40):
        if (n-k)%2: continue
        phase = (-1)**((n-k)//2)
        Bm[n,k]=Bm[k,n] = (2/(2*math.pi))*np.sum(w*(xs<xi0)*special.spherical_jn(n,a*xs)*special.spherical_jn(k,a*xs))*(2*a)**2*math.sqrt((2*n+1)*(2*k+1))/(2*a)*phase
lam = np.sort(np.linalg.eigvalsh(Bm))[::-1]
print("band-limiting concentration eigenvalues (c=%.3f): " % (a*xi0), np.round(lam[:6], 5))
C = constraints(S, 40); u_, s_, vt = np.linalg.svd(C); Bn = vt[2:].T
lamc = np.sort(np.linalg.eigvalsh(Bn.T @ Bm @ Bn))[::-1]
print("constrained (V0) concentration eigenvalues:", np.round(lamc[:4], 5))
print("Legendre tail: |G_nn| and A+Lambda at the mode's frequency scale: n, G_nn:", [(n, round(G[n,n],3)) for n in (10, 20, 30, 39)])

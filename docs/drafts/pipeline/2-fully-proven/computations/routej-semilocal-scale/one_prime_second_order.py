#!/usr/bin/env python3
"""MUST-176: the one-prime second-order response.
 True Euler weight E_eps(s) = 1/(1 - 2 eps cos(d s) + eps^2), d = log p, eps = p^{-1/2}.
 Claim: [eps^2] log D_n = (n+1) + J_{2d}(n) - (1/2) tr(T(d)^2),   J_d(n) = tr T(d)_n = 2 sum_{i<=n} m_i(d).
        [eps^2] a_n^2 = r_n^2 [ DDJ_{2d}(n) - (1/2) DD D_d(n) + (1/2) (DDJ_d(n))^2 ],  DD f(n) = f(n-1) + f(n+1) - 2 f(n).
 Checks: finite differences of the true Euler weight (log det, squared radius); sizes eps*[eps] vs eps^2*[eps^2];
         and against the non-perturbative deviation a_n^2(eps)/r_n^2 - 1."""
import numpy as np, math
from scipy.special import loggamma
def basis(nmax, T, ds):
    s = np.arange(-T, T + ds/2, ds)
    logw = 2*np.real(loggamma(0.25 + 0.5j*s)); logw -= logw.max()
    w = np.exp(logw)*ds; w /= w.sum()
    q = np.zeros((nmax+1, len(s))); q[0] = np.sqrt(w)
    r = lambda n: math.sqrt((n+0.5)*(n+1))
    q[1] = s*q[0]/r(0)
    for n in range(1, nmax): q[n+1] = (s*q[n] - r(n-1)*q[n-1])/r(n)
    return s, q
def tangent(q, s, d): return 2*(q*np.cos(d*s)) @ q.T
def logdet_gram(q, s, f): return np.linalg.slogdet((q*f) @ q.T)[1]
def rsq(n): return (n+0.5)*(n+1)
p = 211; d = math.log(p); eps0 = p**-0.5
nmax = 160; T = 2.2*nmax + 80; ds = 0.004
s, q = basis(nmax, T, ds)
print("orthonormality:", np.abs(q @ q.T - np.eye(nmax+1)).max())
Td = tangent(q, s, d); T2d = tangent(q, s, 2*d)
J1 = np.array([np.trace(Td[:n+1, :n+1]) for n in range(nmax+1)])
J2 = np.array([np.trace(T2d[:n+1, :n+1]) for n in range(nmax+1)])
Dd = np.array([np.trace(Td[:n+1, :n+1] @ Td[:n+1, :n+1]) for n in range(nmax+1)])
def euler(e): return 1.0/(1 - 2*e*np.cos(d*s) + e*e)
def trunc(e): return 1 + 2*e*np.cos(d*s) + e*e*(1 + 2*np.cos(2*d*s))
print("(1) [eps^2] log D_n: formula vs symmetric second difference of the true Euler weight (e = 1e-3):")
e = 1e-3
for n in (3, 8, 12, 30):
    qn = q[:n+1]
    fd = (logdet_gram(qn, s, euler(e)) - 2*logdet_gram(qn, s, euler(0)) + logdet_gram(qn, s, euler(-e)))/(2*e*e)
    fdt = (logdet_gram(qn, s, trunc(e)) - 2*logdet_gram(qn, s, trunc(0)) + logdet_gram(qn, s, trunc(-e)))/(2*e*e)
    form = (n+1) + J2[n] - 0.5*Dd[n]
    print("   n=%d: formula=%.8f  fd(Euler)=%.8f  fd(trunc)=%.8f" % (n, form, fd, fdt))
# radius level
def DD(f, n): return f[n-1] + f[n+1] - 2*f[n]
def a2_from_logdets(L, n):  # a_n^2 = r^2 D_{n-1} D_{n+1}/D_n^2 with L = log D
    return rsq(n)*math.exp(L[n-1] + L[n+1] - 2*L[n])
print("(2) [eps^2] a_n^2: formula vs finite difference (true Euler):")
for n in (3, 8, 12, 30):
    Lp = np.array([logdet_gram(q[:m+1], s, euler(e)) for m in range(n+2)])
    L0 = np.array([logdet_gram(q[:m+1], s, euler(0)) for m in range(n+2)])
    Lm = np.array([logdet_gram(q[:m+1], s, euler(-e)) for m in range(n+2)])
    fd = (a2_from_logdets(Lp, n) - 2*a2_from_logdets(L0, n) + a2_from_logdets(Lm, n))/(2*e*e)
    form = rsq(n)*(DD(J2, n) - 0.5*DD(Dd, n) + 0.5*DD(J1, n)**2)
    print("   n=%d: formula=%.8f  fd=%.8f  (harmonic part=%.3e, variance part=%.3e, square part=%.3e)" % (n, form, fd, rsq(n)*DD(J2,n), -0.5*rsq(n)*DD(Dd,n), 0.5*rsq(n)*DD(J1,n)**2))
print("(3) sizes at eps = p^{-1/2} = %.4f: first-order eps*[eps]a^2/r^2 vs second-order eps^2*[eps^2]a^2/r^2 vs exact (a_n^2(eps)/r^2 - 1):" % eps0)
Le = np.array([logdet_gram(q[:m+1], s, euler(eps0)) for m in range(nmax+1)])
for n in (10, 20, 50, 100, 150):
    first = eps0*DD(J1, n); second = eps0**2*(DD(J2, n) - 0.5*DD(Dd, n) + 0.5*DD(J1, n)**2)
    exact = math.exp(Le[n-1] + Le[n+1] - 2*Le[n]) - 1
    print("   n=%d: first=%.6e  second=%.3e  first+second=%.6e  exact=%.6e  exact-first=%.2e  exact-first-second=%.2e" % (n, first, second, first+second, exact, exact-first, exact-first-second))

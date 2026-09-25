#!/usr/bin/env python3
"""MUST-178: finite-S second-order assembly along a ray eps = t v.
 Q(v) := (d/dt)^2 log D_n(t v)|_0 = sum_{a,b} v_a v_b B_ab(n) + sum_a v_a^2 J_{2 d_a}(n),
   B_ab = J_{d_a+d_b} + J_{d_a-d_b} - tr(T_a T_b)  (bilinear jet; a=b allowed, J_0 = 2(n+1)).
 Radius level: (d/dt)^2 a_n^2(tv)|_0 = r^2 [ DD Q(v)(n) + (sum_a v_a DDJ_{d_a}(n))^2 ].
 Checks against finite differences of the TRUE Euler product weight prod_a 1/(1 - 2 t v_a cos(d_a s) + t^2 v_a^2)."""
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
def logdet(q, s, f): return np.linalg.slogdet((q*f) @ q.T)[1]
def rsq(n): return (n+0.5)*(n+1)
primes = [101, 211, 307]
ds_ = [math.log(p) for p in primes]; v = [p**-0.5 for p in primes]
nmax = 120; T = 2.2*nmax + 80; ds = 0.004
s, q = basis(nmax, T, ds)
print("orthonormality:", np.abs(q @ q.T - np.eye(nmax+1)).max())
Tm = {d: tangent(q, s, d) for d in set(ds_ + [2*d for d in ds_] + [da+db for da in ds_ for db in ds_] + [da-db for da in ds_ for db in ds_])}
def J(d, n): return np.trace(Tm[d][:n+1,:n+1])
def B(da, db, n): return J(da+db, n) + J(da-db, n) - np.trace(Tm[da][:n+1,:n+1] @ Tm[db][:n+1,:n+1])
def Q(n): return sum(v[a]*v[b]*B(ds_[a], ds_[b], n) for a in range(3) for b in range(3)) + sum(v[a]**2*J(2*ds_[a], n) for a in range(3))
def euler(t): 
    f = np.ones_like(s)
    for a in range(3): f = f/(1 - 2*t*v[a]*np.cos(ds_[a]*s) + (t*v[a])**2)
    return f
print("(1) Q(v) vs second difference of log det of the true Euler product along the ray (h = 1e-2):")
h = 1e-2
for n in (3, 8, 20, 40):
    qn = q[:n+1]
    fd = (logdet(qn, s, euler(h)) - 2*logdet(qn, s, euler(0)) + logdet(qn, s, euler(-h)))/h**2
    print("   n=%d: Q=%.8f  fd=%.8f  diff=%.1e" % (n, Q(n), fd, Q(n)-fd))
def DD(f, n): return f(n-1) + f(n+1) - 2*f(n)
print("(2) radius level: r^2[DD Q + (sum_a v_a DDJ_a)^2] vs finite difference:")
for n in (3, 8, 20, 40):
    form = rsq(n)*(DD(Q, n) + sum(v[a]*DD(lambda m: J(ds_[a], m), n) for a in range(3))**2)
    L = lambda t: np.array([logdet(q[:m+1], s, euler(t)) for m in range(n+2)])
    a2 = lambda Lv: rsq(n)*math.exp(Lv[n-1] + Lv[n+1] - 2*Lv[n])
    fd = (a2(L(h)) - 2*a2(L(0)) + a2(L(-h)))/h**2
    print("   n=%d: formula=%.8f  fd=%.8f  diff=%.1e" % (n, form, fd, form-fd))
print("(3) the finite-S deviation a_n^2(v)/r^2 - 1 at t = 1 vs first order sum_a v_a DDJ_a and second order (1/2)[DD Q + (sum v DDJ)^2]:")
L1 = np.array([logdet(q[:m+1], s, euler(1.0)) for m in range(nmax+1)])
for n in (10, 20, 50, 100):
    first = sum(v[a]*DD(lambda m: J(ds_[a], m), n) for a in range(3))
    second = 0.5*(DD(Q, n) + first**2)
    exact = math.exp(L1[n-1] + L1[n+1] - 2*L1[n]) - 1
    cross = sum(v[a]*v[b]*DD(lambda m: B(ds_[a], ds_[b], m), n) for a in range(3) for b in range(3) if a != b)
    print("   n=%d: first=%.6e  second=%.3e (cross part %.3e)  exact=%.6e  exact-first=%.2e  exact-first-second=%.2e" % (n, first, second, 0.5*cross, exact, exact-first, exact-first-second))

#!/usr/bin/env python3
"""MUST-180 pre-certification: the determinant-level Taylor remainder for the TRUE Euler product.
 Claim: log det G_W(n) = tr M1 + tr M2 - (1/2) tr M1^2 + R,  |R| = O(eps^3), where
   M1 = sum_a eps_a T(d_a),  M2 = (1/2) sum_{a,b} eps_a eps_b (T(d_a+d_b)+T(d_a-d_b)) + (1/2) sum_a eps_a^2 T(2 d_a).
 Equivalently  log det G_W = sum_a eps_a J_{d_a} + (1/2)[sum_{ab} eps_a eps_b B_ab + sum_a eps_a^2 J_{2d_a}] + R.
 Scaling test: eps -> lambda eps, remainder should scale like lambda^3.
 Also: the crude entry-norm constants of the Lean theorem (eta = (n+1)^2 (2V + 3V^2 + rho)) vs the true size."""
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
primes = [101, 211, 307]
ds_ = [math.log(p) for p in primes]; v0 = [p**-0.5 for p in primes]
nmax = 60; T = 2.2*nmax + 80; ds = 0.004
s, q = basis(nmax, T, ds)
print("orthonormality:", np.abs(q @ q.T - np.eye(nmax+1)).max())
keys = set(ds_ + [2*d for d in ds_] + [da+db for da in ds_ for db in ds_] + [da-db for da in ds_ for db in ds_])
Tm = {d: tangent(q, s, d) for d in keys}
def gram(f, n): return (q[:n+1]*f) @ q[:n+1].T
def euler(eps):
    f = np.ones_like(s)
    for a in range(3): f = f/(1 - 2*eps[a]*np.cos(ds_[a]*s) + eps[a]**2)
    return f
def M1(eps, n): return sum(eps[a]*Tm[ds_[a]][:n+1,:n+1] for a in range(3))
def M2(eps, n):
    A = 0.5*sum(eps[a]*eps[b]*(Tm[ds_[a]+ds_[b]][:n+1,:n+1] + Tm[ds_[a]-ds_[b]][:n+1,:n+1]) for a in range(3) for b in range(3))
    return A + 0.5*sum(eps[a]**2*Tm[2*ds_[a]][:n+1,:n+1] for a in range(3))
print("(1) log det G_W vs second-order jet tr M1 + tr M2 - tr(M1^2)/2; remainder R and its scaling under eps -> eps/2:")
for n in (2, 5, 10, 20, 40):
    prev = None
    for lam in (1.0, 0.5, 0.25, 0.125):
        eps = [lam*x for x in v0]
        G = gram(euler(eps), n)
        L = np.linalg.slogdet(G)[1]
        m1 = M1(eps, n); m2 = M2(eps, n)
        jet = np.trace(m1) + np.trace(m2) - 0.5*np.trace(m1 @ m1)
        R = L - jet
        N = G - np.eye(n+1)
        eta = np.abs(N).sum(); V = sum(eps)
        ratio = (prev/R) if prev is not None and R != 0 else float('nan')
        print("   n=%d lam=%.3f: logdet=%.8f jet=%.8f R=%.3e  ratio(prev/R)=%.2f  ||N||_1=%.3e  ||N||_op=%.3e  V=%.3e  first-order=%.3e" % (n, lam, L, jet, R, ratio, eta, np.linalg.norm(N, 2), V, np.trace(m1)))
        prev = R
print("(2) log-det-level identity of the jet with the corpus jets: sum_a eps_a J_a + (1/2)[sum eps eps B_ab + sum eps^2 J_{2d}] (n=10):")
n = 10; eps = v0
J = lambda d: np.trace(Tm[d][:n+1,:n+1])
B = lambda da, db: J(da+db) + J(da-db) - np.trace(Tm[da][:n+1,:n+1] @ Tm[db][:n+1,:n+1])
jet2 = sum(eps[a]*J(ds_[a]) for a in range(3)) + 0.5*(sum(eps[a]*eps[b]*B(ds_[a], ds_[b]) for a in range(3) for b in range(3)) + sum(eps[a]**2*J(2*ds_[a]) for a in range(3)))
m1 = M1(eps, n); m2 = M2(eps, n)
print("   trace form = %.10f   corpus-jet form = %.10f   diff = %.1e" % (np.trace(m1) + np.trace(m2) - 0.5*np.trace(m1 @ m1), jet2, np.trace(m1) + np.trace(m2) - 0.5*np.trace(m1 @ m1) - jet2))
print("(3) sup |W - W2| (W2 = 1 + A + B) vs the Lean bound (3/2)^k*60*sum eps^3 + 12800 V^3, and sup|W-1|:")
for lam in (1.0, 0.5, 0.25):
    eps = [lam*x for x in v0]
    A = sum(2*eps[a]*np.cos(ds_[a]*s) for a in range(3)); Bq = 0.5*A**2 + sum(eps[a]**2*np.cos(2*ds_[a]*s) for a in range(3))
    W = euler(eps); V = sum(eps)
    print("   lam=%.3f: sup|W-W2|=%.3e  bound=%.3e  sup|W-1|=%.3e  3V=%.3e" % (lam, np.abs(W - 1 - A - Bq).max(), 1.5**3*60*sum(e**3 for e in eps) + 12800*V**3, np.abs(W-1).max(), 3*V))
print("(4) Hankel level: log(a_n^2/r_n^2) = DD log det; remainder of the second-order jet at the log level, n=5,10,20 (lam=1, 1/2):")
def DDlog(f, n): return f(n-1) + f(n+1) - 2*f(n)
for n in (5, 10, 20):
    for lam in (1.0, 0.5):
        eps = [lam*x for x in v0]
        Lf = lambda m: np.linalg.slogdet(gram(euler(eps), m))[1]
        jf = lambda m: (lambda m1, m2: np.trace(m1) + np.trace(m2) - 0.5*np.trace(m1 @ m1))(M1(eps, m), M2(eps, m))
        print("   n=%d lam=%.2f: DD logdet=%.6e  DD jet=%.6e  remainder=%.2e" % (n, lam, DDlog(Lf, n), DDlog(jf, n), DDlog(Lf, n) - DDlog(jf, n)))

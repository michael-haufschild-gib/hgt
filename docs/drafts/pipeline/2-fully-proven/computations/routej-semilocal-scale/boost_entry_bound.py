#!/usr/bin/env python3
"""MUST-173: separable expansion and bound for the boost matrix elements M_mn(t) = int p_m p_n e^{its} dmu.
 Exact:  c_m c_n M_mn(t) = (cosh t)^{-1/2} sum_{k<=min(m,n)} C_k sigma^{2k} (i tau)^{m+n-2k} ((k+1/2)_{m-k}/(m-k)!) ((k+1/2)_{n-k}/(n-k)!)
 (sigma = sech t, tau = tanh t, C_k = binom(2k,k)/4^k, c_k = sqrt(C_k)).
 Bound:  |M_mn(t)| <= (cosh t)^{-1/2} c_m c_n tau^{m+n} cosh(2 sqrt(mn)/sinh t) <= (cosh t)^{-1/2} c_m c_n exp(2mn/sinh^2 t).
 Checks: (a) exact formula vs quadrature (small m,n, moderate t); (b) row polynomial identity (z+i tau)^m = sum_k a_{mk} z^k (1-i tau z)^{m-k};
         (c) bound vs exact for t = log 211, m,n <= 150."""
from mpmath import mp, mpf, mpc, binomial, sqrt, cosh, sinh, tanh, exp, quad, gamma, rf, factorial, pi, log, loggamma, cos, sin
import random
mp.dps = 30
def C(k): return binomial(2*k, k)/mpf(4)**k
def c(k): return sqrt(C(k))
def Mexact(m, n, t):
    s = 1/cosh(t); tau = tanh(t)
    tot = mpc(0)
    for k in range(min(m, n)+1):
        tot += C(k)*s**(2*k)*(1j*tau)**(m+n-2*k)*(rf(k+mpf(1)/2, m-k)/factorial(m-k))*(rf(k+mpf(1)/2, n-k)/factorial(n-k))
    return cosh(t)**(-mpf(1)/2)*tot/(c(m)*c(n))
def bound(m, n, t):
    return cosh(t)**(-mpf(1)/2)*c(m)*c(n)*tanh(t)**(m+n)*cosh(2*sqrt(mpf(m*n))/sinh(t))
# (a) quadrature: orthonormal polynomials via recurrence r_n = sqrt((n+1/2)(n+1)), weight |Gamma(1/4+is/2)|^2 normalised
def pvals(N, s):
    r = lambda n: sqrt((n+mpf(1)/2)*(n+1))
    p = [mpf(1)]
    if N >= 1: p.append(s/r(0))
    for n in range(1, N):
        p.append((s*p[n] - r(n-1)*p[n-1])/r(n))
    return p
Z = quad(lambda s: exp(2*loggamma(mpf(1)/4 + 0.5j*s).real), [-mp.inf, mp.inf])
def Mquad(m, n, t):
    f = lambda s: (lambda P: P[m]*P[n])(pvals(max(m,n), s))*exp(2*loggamma(mpf(1)/4 + 0.5j*s).real)*exp(1j*t*s)/Z
    return quad(f, [-mp.inf, -20, 0, 20, mp.inf])
print("(a) exact vs quadrature:")
for (m, n, t) in ((0, 0, mpf(1)), (1, 0, mpf(1)), (2, 3, mpf('0.7')), (4, 4, mpf('1.5')), (5, 2, mpf(3))):
    e, q = Mexact(m, n, t), Mquad(m, n, t)
    print("   m=%d n=%d t=%.2f: exact=%s  quad=%s  |diff|=%.1e" % (m, n, t, mp.nstr(e, 12), mp.nstr(q, 12), abs(e-q)))
# (b) polynomial identity
print("(b) row polynomial identity max err:")
err = mpf(0)
for m in range(0, 8):
    for _ in range(3):
        t = mpf(random.random()*3+0.1); z = mpc(random.random()-0.5, random.random()-0.5)
        s = 1/cosh(t); tau = tanh(t)
        rhs = sum((C(k)/C(m))*s**(2*k)*(rf(k+mpf(1)/2, m-k)/factorial(m-k))*(1j*tau)**(m-k)*z**k*(1-1j*tau*z)**(m-k) for k in range(m+1))
        err = max(err, abs((z+1j*tau)**m - rhs))
print("   ", err)
# (c) bound vs exact at t = log 211
t = log(mpf(211)); worst = mpf(0)
print("(c) t = log 211: |M|/((cosh)^-1/2 c_m c_n) and bound/exact:")
for (m, n) in ((0, 0), (1, 1), (5, 5), (10, 10), (20, 20), (20, 50), (50, 50), (100, 100), (150, 150), (30, 150)):
    e = abs(Mexact(m, n, t)); b = bound(m, n, t); base = cosh(t)**(-mpf(1)/2)*c(m)*c(n)
    worst = max(worst, e/b)
    print("   m=%d n=%d: |M|/base=%.6f  bound/base=%.6f  exact/bound=%.4f  exp-bound/base=%.4f" % (m, n, e/base, b/base, e/b, exp(2*mpf(m*n)/sinh(t)**2)))
print("   max exact/bound =", worst)
# small t sanity
for t in (mpf('0.3'), mpf(1), mpf(2)):
    worst = max(abs(Mexact(m, n, t))/bound(m, n, t) for m in range(0, 12) for n in range(0, 12))
    print("   t=%.1f: max exact/bound over m,n<12 =" % t, mp.nstr(worst, 6))

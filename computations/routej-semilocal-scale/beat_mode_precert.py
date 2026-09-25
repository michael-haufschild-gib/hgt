#!/usr/bin/env python3
"""Pre-certification for MUST-150 (beat mode, fixed delta).
 (a) Legendre identification: S_n(tau) = P_{2n}(sigma), sigma = sech delta, tau = tanh delta.
 (b) convolution: P_N(cos phi) = sum_k C_k C_{N-k} cos((N-2k) phi).
 (c) Laplace-Heine: P_N(cos phi) = 2 C_N (2 sin phi)^{-1/2} cos((N+1/2)phi - pi/4) + O(1/N).
 (d) exact residual: J_k(delta) = (cosh d)^{-1/2} [ r_{2k} r_{2k+1} (P_{4k+4}-P_{4k}) - 2 r_{2k+1}^2 (P_{4k+4}-P_{4k+2})
        - 2 r_{2k+2}^2 (P_{4k+6}-P_{4k+4}) + r_{2k+2} r_{2k+3} (P_{4k+8}-P_{4k+4}) ]  (P_N = P_N(sigma))
 (e) beat law: J_k(delta) ~ 32 sqrt(2/pi) k^{3/2} sigma^{3/2} tau^{5/2} sin((4k+9/2) phi - pi/4), phi = arccos sigma."""
from mpmath import mp, mpf, hyp2f1, legendre, binomial, cos, sin, sqrt, pi, acos, cosh, tanh, log
import random
mp.dps = 30; random.seed(5)
def C(n): return binomial(2*n, n)/mpf(4)**n
def S(n, tau): return hyp2f1(-n, n+mpf(1)/2, 1, tau**2)
e=0
for n in range(0, 12):
    for _ in range(3):
        d = mpf(random.random()*3+0.05); e = max(e, abs(S(n, tanh(d)) - legendre(2*n, 1/cosh(d))))
print("(a) S_n(tanh d) = P_{2n}(sech d): max abs err", e)
e=0
for N in range(0, 15):
    for _ in range(3):
        phi = mpf(random.random()*3+0.05)
        conv = sum(C(k)*C(N-k)*cos((N-2*k)*phi) for k in range(N+1))
        e = max(e, abs(conv - legendre(N, cos(phi))))
print("(b) convolution identity: max abs err", e)
phi = mpf(1.1)
for N in (100, 1000, 10000):
    asym = 2*C(N)*(2*sin(phi))**(-mpf(1)/2)*cos((N+mpf(1)/2)*phi - pi/4)
    print("(c) N=%d: P_N=%.8f asym=%.8f  N*(diff)=%.5f"%(N, legendre(N, cos(phi)), asym, N*(legendre(N, cos(phi)) - asym)))
def r(n): return sqrt((n+mpf(1)/2)*(n+1))
def Jexact(k, d):
    s = 1/cosh(d); tau = tanh(d); ch = cosh(d)**(-mpf(1)/2)
    m = lambda n: ch*S(n, tau)
    u = lambda n: r(n)*(m(n+1)-m(n))
    return u(2*k)*r(2*k+1) + r(2*k)*u(2*k+1) - 2*r(2*k+1)*u(2*k+1) - 2*r(2*k+2)*u(2*k+2) + u(2*k+2)*r(2*k+3) + r(2*k+2)*u(2*k+3)
def Jleg(k, d):
    s = 1/cosh(d); ch = cosh(d)**(-mpf(1)/2); P = lambda N: legendre(N, s)
    return ch*( r(2*k)*r(2*k+1)*(P(4*k+4)-P(4*k)) - 2*r(2*k+1)**2*(P(4*k+4)-P(4*k+2)) - 2*r(2*k+2)**2*(P(4*k+6)-P(4*k+4)) + r(2*k+2)*r(2*k+3)*(P(4*k+8)-P(4*k+4)) )
def Jbeat(k, d):
    s = 1/cosh(d); tau = tanh(d); phi = acos(s)
    return 32*sqrt(2/pi)*mpf(k)**mpf(1.5)*s**mpf(1.5)*tau**mpf(2.5)*sin((4*k+mpf(9)/2)*phi - pi/4)
e=0
for k in range(1, 9):
    for _ in range(2):
        d = mpf(random.random()*2+0.2); e = max(e, abs(Jexact(k,d)/Jleg(k,d) - 1))
print("(d) exact residual = Legendre combination: max rel err", e)
for d in (mpf(log(3)/log(2)*0+0.6931), log(mpf(3)/2), log(mpf(7)/5)):   # delta = log 2, log 1.5, log 1.4
    for k in (50, 200, 800, 3200):
        print("(e) delta=%.4f k=%d: J=%.6g  beat=%.6g  ratio=%.5f  |J|/k^1.5=%.5f"%(d, k, Jleg(k,d), Jbeat(k,d), Jleg(k,d)/Jbeat(k,d), abs(Jleg(k,d))/mpf(k)**1.5))

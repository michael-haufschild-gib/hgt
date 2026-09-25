#!/usr/bin/env python3
"""Numerical pre-certification of the Mehler-Heine / residual-jet programme (MUST-149).
 S_n(tau)   := sum_l C(n,l) Ring.choose(-(n+1/2), l) tau^{2l}          (Lean-proved diagonal, tau-form)
 F_n(sigma) := 2F1(-n, n+1/2; 1/2; sigma^2),  sigma^2 = 1 - tau^2
 (a) Pfaff:  S_n(tau) = (-1)^n C_n F_n(sigma),  C_n = binom(2n,n)/4^n
 (b) contiguous: S_{n+1}-S_n = -(n+3/4)/(n+1) * 2 tau^2 * P_n^{(1,-1/2)}(y),  y = 1-2tau^2
     with P_n^{(1,-1/2)}(y) = (-1)^n (1/2)_n/n! * 2F1(-n, n+3/2; 1/2; sigma^2)
 (c) T_n := (-1)^n P_n^{(1,-1/2)}(y);  (n+1)(T_{n+1}-T_n) = -(n+5/4) 2 sigma^2 P_n^{(1/2,1)}(x) - T_n/2,
     P_n^{(1/2,1)}(x) = (3/2)_n/n! 2F1(-n, n+5/2; 3/2; sigma^2), x = 1-2 sigma^2
 (d) residual jet identity: with m_n = (cosh d)^{-1/2} S_n, u_n = r_n (m_{n+1}-m_n), r_n = sqrt((n+1/2)(n+1)),
     J_k = u_{2k} r_{2k+1} + r_{2k} u_{2k+1} - 2 r_{2k+1} u_{2k+1} - 2 r_{2k+2} u_{2k+2} + u_{2k+2} r_{2k+3} + r_{2k+2} u_{2k+3}
         = (cosh d)^{-1/2} [ r_{2k} r_{2k+1} (Q_{2k+1}-Q_{2k}) + 2 (r_{2k+2}^2 Q_{2k+2} - r_{2k+1}^2 Q_{2k+1}) + r_{2k+2} r_{2k+3} (Q_{2k+3}-Q_{2k+2}) ]
     with Q_n := (-1)^{n+1} (S_{n+1} - S_n)
 (e) scaling: d = log p, n = 2k ~ x p:  J_k / R_k(0) -> Phi(x) = 4 sqrt(2/pi) [sqrt x cos 4x - 8 x^{3/2} sin 4x]"""
from mpmath import mp, mpf, binomial, hyp2f1, rf, sqrt, cosh, tanh, log, cos, sin, pi, factorial
import random
mp.dps = 40
def C(n): return binomial(2*n, n)/mpf(4)**n
def ringchoose(a, l): return rf(a - l + 1, l)/factorial(l)   # a(a-1)...(a-l+1)/l!
def S_tau(n, tau):
    return sum(binomial(n, l)*ringchoose(-(n+mpf(1)/2), l)*tau**(2*l) for l in range(n+1))
def F(n, s2): return hyp2f1(-n, n+mpf(1)/2, mpf(1)/2, s2)
def S_sigma(n, s2): return (-1)**n * C(n) * F(n, s2)
random.seed(1)
print("(a) Pfaff max rel err:", max(abs(S_tau(n, tau)/S_sigma(n, 1-tau**2) - 1) for n in range(0, 13) for tau in [mpf(random.random()*0.95) for _ in range(3)]))
def Ppoly(n, alpha, beta, s2):   # P_n^{(alpha,beta)}(1 - 2 s2) = (alpha+1)_n/n! 2F1(-n, n+alpha+beta+1; alpha+1; s2)
    return rf(alpha+1, n)/factorial(n)*hyp2f1(-n, n+alpha+beta+1, alpha+1, s2)
def P_1_mhalf_at_y(n, s2):       # P_n^{(1,-1/2)}(y), y = -1 + 2 s2 = -(1 - 2 s2):  = (-1)^n P_n^{(-1/2,1)}(1-2 s2)
    return (-1)**n * Ppoly(n, -mpf(1)/2, 1, s2)
errs=[]
for n in range(0, 12):
    for _ in range(3):
        tau = mpf(random.random()*0.95); s2 = 1 - tau**2
        lhs = S_tau(n+1, tau) - S_tau(n, tau)
        rhs = -(n + mpf(3)/4)/(n+1) * 2*tau**2 * P_1_mhalf_at_y(n, s2)
        errs.append(abs(lhs/rhs - 1))
print("(b) contiguous difference identity max rel err:", max(errs))
errs=[]
for n in range(0, 12):
    for _ in range(3):
        s2 = mpf(random.random()*0.9)
        T = lambda m: (-1)**m * P_1_mhalf_at_y(m, s2)
        lhs = (n+1)*(T(n+1) - T(n))
        rhs = -(n + mpf(5)/4)*2*s2*Ppoly(n, mpf(1)/2, 1, s2) - T(n)/2
        errs.append(abs(lhs/rhs - 1))
print("(c) T-difference identity max rel err:", max(errs))
def r(n): return sqrt((n+mpf(1)/2)*(n+1))
errs=[]
for k in range(0, 8):
    for _ in range(2):
        d = mpf(random.random()*2+0.1); tau = tanh(d); ch = cosh(d)**(-mpf(1)/2)
        S = lambda n: S_sigma(n, 1-tau**2)
        m = lambda n: ch*S(n)
        u = lambda n: r(n)*(m(n+1)-m(n))
        J = u(2*k)*r(2*k+1) + r(2*k)*u(2*k+1) - 2*r(2*k+1)*u(2*k+1) - 2*r(2*k+2)*u(2*k+2) + u(2*k+2)*r(2*k+3) + r(2*k+2)*u(2*k+3)
        Q = lambda n: (-1)**(n+1)*(S(n+1)-S(n))
        J2 = ch*( r(2*k)*r(2*k+1)*(Q(2*k+1)-Q(2*k)) + 2*(r(2*k+2)**2*Q(2*k+2) - r(2*k+1)**2*Q(2*k+1)) + r(2*k+2)*r(2*k+3)*(Q(2*k+3)-Q(2*k+2)) )
        errs.append(abs(J/J2-1))
print("(d) residual difference identity max rel err:", max(errs))
def Phi(x): return 4*sqrt(2/pi)*(sqrt(x)*cos(4*x) - 8*x**mpf(1.5)*sin(4*x))
mp.dps = 30
for p in (1000, 4000, 16000):
    d = log(mpf(p)); tau = tanh(d); s2 = 1 - tau**2; ch = cosh(d)**(-mpf(1)/2)
    row=[]
    for x in (0.3, 0.6, 1.0, 1.269, 2.024):
        k = int(round(x*p/2)); xk = mpf(2*k)/p
        S = lambda n: S_sigma(n, s2); m = lambda n: ch*S(n); u = lambda n: r(n)*(m(n+1)-m(n))
        J = u(2*k)*r(2*k+1) + r(2*k)*u(2*k+1) - 2*r(2*k+1)*u(2*k+1) - 2*r(2*k+2)*u(2*k+2) + u(2*k+2)*r(2*k+3) + r(2*k+2)*u(2*k+3)
        R0 = r(2*k)*r(2*k+1) - r(2*k+1)**2 - r(2*k+2)**2 + r(2*k+2)*r(2*k+3)
        row.append((float(xk), float(J/R0), float(Phi(xk))))
    print("(e) p=%d:"%p, ["x=%.3f J/R0=%.4f Phi=%.4f"%t for t in row])

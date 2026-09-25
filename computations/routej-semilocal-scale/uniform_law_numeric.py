#!/usr/bin/env python3
"""MUST-170 numeric validation: J_k(delta) = sigma^{1/2} (a P_{N+3} + b P_{N+4}) exactly (recurrence reduction),
uniform main term M = sigma^{1/2} A [a cos psi_3 + b cos psi_4], A = 2 C_N (2 tau)^{-1/2}, psi_j = (N+j+1/2) phi - pi/4,
error J - M against the bound sigma^{1/2}(|a|+|b|) 400/(N tau), in the beat regime and in the scaling regime."""
from mpmath import mp, mpf, binomial, cos, sin, sqrt, pi, acos, cosh, tanh, log
mp.dps = 30
_cache = {}
def legendre(n, x):
    key = (n, x)
    if key in _cache: return _cache[key]
    p0, p1 = mpf(1), x
    if n == 0: return p0
    for m in range(1, n):
        p0, p1 = p1, ((2*m+1)*x*p1 - m*p0)/(m+1)
    _cache[key] = p1
    return p1
def C(n): return binomial(2*n, n)/mpf(4)**n
def r(n): return sqrt((n+mpf(1)/2)*(n+1))
def coeffs(k, s):
    N = 4*k
    A = {3: mpf(1), 4: mpf(0)}; B = {3: mpf(0), 4: mpf(1)}
    for j in range(5, 9):
        m = N + j - 2
        A[j] = ((2*m+3)*s*A[j-1] - (m+1)*A[j-2])/(m+2)
        B[j] = ((2*m+3)*s*B[j-1] - (m+1)*B[j-2])/(m+2)
    for j in (2, 1, 0):
        m = N + j
        A[j] = ((2*m+3)*s*A[j+1] - (m+2)*A[j+2])/(m+1)
        B[j] = ((2*m+3)*s*B[j+1] - (m+2)*B[j+2])/(m+1)
    R1 = r(2*k)*r(2*k+1); R2 = r(2*k+2)*r(2*k+3); r1sq = r(2*k+1)**2; r2sq = r(2*k+2)**2
    a = R1*(A[4]-A[0]) - 2*r1sq*(A[4]-A[2]) - 2*r2sq*(A[6]-A[4]) + R2*(A[8]-A[4])
    b = R1*(B[4]-B[0]) - 2*r1sq*(B[4]-B[2]) - 2*r2sq*(B[6]-B[4]) + R2*(B[8]-B[4])
    return a, b
def Jleg(k, d):
    s = 1/cosh(d); ch = cosh(d)**(-mpf(1)/2); P = lambda N: legendre(N, s)
    return ch*( r(2*k)*r(2*k+1)*(P(4*k+4)-P(4*k)) - 2*r(2*k+1)**2*(P(4*k+4)-P(4*k+2)) - 2*r(2*k+2)**2*(P(4*k+6)-P(4*k+4)) + r(2*k+2)*r(2*k+3)*(P(4*k+8)-P(4*k+4)) )
def analyse(k, d, tag):
    s = 1/cosh(d); tau = tanh(d); phi = acos(s); N = 4*k
    a, b = coeffs(k, s)
    J = Jleg(k, d)
    two = sqrt(s)*(a*legendre(N+3, s) + b*legendre(N+4, s))
    Aamp = 2*C(N)*(2*tau)**(-mpf(1)/2)
    psi = lambda j: (N+j+mpf(1)/2)*phi - pi/4
    M = sqrt(s)*Aamp*(a*cos(psi(3)) + b*cos(psi(4)))
    bound = sqrt(s)*(abs(a)+abs(b))*400/(N*tau)
    beat = 32*sqrt(2/pi)*mpf(k)**mpf(1.5)*s**mpf(1.5)*tau**mpf(2.5)*sin((4*k+mpf(9)/2)*phi - pi/4)
    print("%s k=%d delta=%.4f: |J-two|=%.1e  J=%.6g  M=%.6g  |J-M|=%.3g  bound=%.3g  a/(64k^2 s tau^2)=%.6f  b/(-64k^2 s^2 tau^2)=%.6f  M/beat=%.5f"
          % (tag, k, d, abs(J-two), J, M, abs(J-M), bound, a/(64*k**2*s*tau**2), b/(-64*k**2*s**2*tau**2), M/beat), flush=True)
    return J, M
print("--- beat regime (delta = log 2) ---")
for k in (50, 200, 800, 3200):
    analyse(k, log(mpf(2)), "beat")
print("--- beat regime (delta = log 1.5) ---")
for k in (50, 200, 800, 3200):
    analyse(k, log(mpf(3)/2), "beat")
print("--- small delta (tau small): delta = 0.2 ---")
for k in (200, 3200):
    analyse(k, mpf('0.2'), "smalld")
print("--- scaling regime X = 1.3: k = X p /2, delta = log p ---")
X = mpf('1.3')
Phi = 4*sqrt(2/pi)*(sqrt(X)*cos(4*X) - 8*X**mpf(1.5)*sin(4*X))
print("Phi(X) =", Phi)
for p in (100, 1000, 10000, 40000):
    k = int(mp.nint(X*p/2)); d = log(mpf(p))
    Xk = 2*mpf(k)/p
    Phik = 4*sqrt(2/pi)*(sqrt(Xk)*cos(4*Xk) - 8*Xk**mpf(1.5)*sin(4*Xk))
    J, M = analyse(k, d, "scal")
    print("      X_k=%.6f Phi(X_k)=%.6f  J-Phi=%.2e  M-Phi=%.2e" % (Xk, Phik, J-Phik, M-Phik), flush=True)

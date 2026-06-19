#!/usr/bin/env python3
# Pre-certification for: stieltjes-exponential-period-realization.md
# Claim: gamma_n (Stieltjes constants, Laurent coeffs of zeta at s=1) are exponential periods.
# Construction:  Gamma(s)zeta(s) = int_0^inf t^{s-1}/(e^t-1) dt,  1/(e^t-1)=sum_k e^{-kt},
#                t^{s-1} = sum_m (s-1)^m (log t)^m / m!.
# Local run, sub-second, no runpod.
import mpmath as mp
mp.mp.dps = 30

print("=== (P1) gamma_E = -int_0^inf e^{-x} log x dx = Gamma'(1) ===")
I = -mp.quad(lambda x: mp.e**(-x)*mp.log(x), [0, mp.inf])
print("  integral      :", mp.nstr(I, 20))
print("  mp.euler      :", mp.nstr(mp.euler, 20))
print("  |diff|        :", float(abs(I - mp.euler)))

print("=== Gamma^{(m)}(1) = int_0^inf e^{-x}(log x)^m dx  (exp-period moments) ===")
for m in range(1, 4):
    Im = mp.quad(lambda x: mp.e**(-x)*mp.log(x)**m, [0, mp.inf])
    Dm = mp.diff(mp.gamma, 1, m)
    print("  m=%d  int=%s  Gamma^{(m)}(1)=%s  |diff|=%.1e" %
          (m, mp.nstr(Im, 18), mp.nstr(Dm, 18), float(abs(Im - Dm))))

print("=== new exponential generators J_m = int_1^inf (log t)^m/(e^t-1) dt ===")
for m in range(0, 4):
    Jm = mp.quad(lambda t: mp.log(t)**m/(mp.e**t - 1), [1, mp.inf])
    print("  m=%d  J_m=%s" % (m, mp.nstr(Jm, 18)))

print("=== (P2) Stieltjes regularized-limit formula ===")
def stieltjes_reg(n, M):
    s = mp.mpf(0)
    for k in range(1, M + 1):
        s += (mp.log(k)**n)/k
    return s - (mp.log(M)**(n+1))/(n+1)
for n in range(0, 3):
    print("  n=%d  reg-limit(M=2e5)=%s  mp.stieltjes=%s" %
          (n, mp.nstr(stieltjes_reg(n, 200000), 12), mp.nstr(mp.stieltjes(n), 12)))

print("=== full construction self-consistency: zeta(1+h)-1/h == sum (-1)^n gamma_n/n! h^n ===")
for h in [mp.mpf('0.2'), mp.mpf('0.05')]:
    lhs = mp.zeta(1+h) - 1/h
    rhs = mp.nsum(lambda n: (-1)**int(n)*mp.stieltjes(int(n))/mp.factorial(int(n))*h**int(n), [0, 25])
    print("  h=%s  lhs=%s  series=%s  |diff|=%.1e" %
          (mp.nstr(h, 3), mp.nstr(lhs, 18), mp.nstr(rhs, 18), float(abs(lhs - rhs))))

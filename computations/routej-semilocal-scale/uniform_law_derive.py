#!/usr/bin/env python3
"""MUST-170: exact two-index Legendre form of the Route J residual and the uniform main term.
 B := J_k(delta)/sigma^{1/2} = R1 (P4-P0) - 2 r1sq (P4-P2) - 2 r2sq (P6-P4) + R2 (P8-P4),  P_j = P_{N+j}(sigma), N=4k,
 R1 = r_{2k} r_{2k+1}, R2 = r_{2k+2} r_{2k+3}, r1sq = r_{2k+1}^2, r2sq = r_{2k+2}^2.
 Reduce with the Legendre recurrence to  B = a P_{N+3} + b P_{N+4}  (exact), expand a,b in k."""
import sympy as sp, sys
s, k, R1, R2 = sp.symbols('s k R1 R2', positive=True)
N = 4*k
# P_j = A_j * P3 + B_j * P4 ; store (A_j, B_j) as rational functions, cancel after each step
A = {3: sp.Integer(1), 4: sp.Integer(0)}
Bc = {3: sp.Integer(0), 4: sp.Integer(1)}
for j in range(5, 9):
    m = N + j - 2
    A[j] = sp.cancel(((2*m+3)*s*A[j-1] - (m+1)*A[j-2])/(m+2))
    Bc[j] = sp.cancel(((2*m+3)*s*Bc[j-1] - (m+1)*Bc[j-2])/(m+2))
for j in (2, 1, 0):
    m = N + j
    A[j] = sp.cancel(((2*m+3)*s*A[j+1] - (m+2)*A[j+2])/(m+1))
    Bc[j] = sp.cancel(((2*m+3)*s*Bc[j+1] - (m+2)*Bc[j+2])/(m+1))
print("reduction done", flush=True)
for j in range(9):
    print(f"A_{j} =", sp.factor(A[j]), flush=True)
    print(f"B_{j} =", sp.factor(Bc[j]), flush=True)
r1sq = (2*k+sp.Rational(3,2))*(2*k+2)
r2sq = (2*k+sp.Rational(5,2))*(2*k+3)
a = sp.cancel(R1*(A[4]-A[0]) - 2*r1sq*(A[4]-A[2]) - 2*r2sq*(A[6]-A[4]) + R2*(A[8]-A[4]))
b = sp.cancel(R1*(Bc[4]-Bc[0]) - 2*r1sq*(Bc[4]-Bc[2]) - 2*r2sq*(Bc[6]-Bc[4]) + R2*(Bc[8]-Bc[4]))
print("a =", sp.factor(a), flush=True)
print("b =", sp.factor(b), flush=True)
# pieces: a = R1*aR1 + R2*aR2 + a0
def pieces(expr):
    e = sp.expand(sp.numer(sp.together(expr)))
    den = sp.denom(sp.together(expr))
    pR1 = e.coeff(R1); pR2 = e.coeff(R2); p0 = sp.expand(e - pR1*R1 - pR2*R2)
    return [sp.factor(sp.cancel(x/den)) for x in (pR1, pR2, p0)]
for name, e in (("a", a), ("b", b)):
    pR1, pR2, p0 = pieces(e)
    print(f"{name}_R1 =", pR1, flush=True)
    print(f"{name}_R2 =", pR2, flush=True)
    print(f"{name}_0  =", p0, flush=True)
rho1, rho2 = sp.symbols('rho1 rho2')
eps = sp.symbols('eps', positive=True)
def expand_k(expr, order=3):
    e = sp.cancel(expr.subs({R1: 4*k**2+5*k+rho1, R2: 4*k**2+13*k+rho2}).subs(k, 1/eps))
    ser = sp.series(e, eps, 0, order).removeO()
    return sp.expand(ser.subs(eps, 1/k))
for name, e in (("a", a), ("b", b)):
    ee = expand_k(e)
    pk = sp.Poly(ee, k)
    for (deg,), c in sorted(pk.terms(), reverse=True):
        print(f"{name}: k^{deg} coefficient:", sp.factor(c), flush=True)
kk = sp.symbols('kk', positive=True)
R1e = sp.sqrt((2*kk+sp.Rational(1,2))*(2*kk+1)*(2*kk+sp.Rational(3,2))*(2*kk+2))
R2e = sp.sqrt((2*kk+sp.Rational(5,2))*(2*kk+3)*(2*kk+sp.Rational(7,2))*(2*kk+4))
for name, R in (("R1", R1e), ("R2", R2e)):
    ser = sp.series(R.subs(kk, 1/eps), eps, 0, 4).removeO()
    print(name, "=", sp.expand(ser.subs(eps, 1/kk)), flush=True)
print("DONE", flush=True)

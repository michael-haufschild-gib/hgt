#!/usr/bin/env python3
"""Expansions of the two-index coefficients a, b (closed forms from uniform_law_derive.log)."""
import sympy as sp
s, k = sp.symbols('s k', positive=True)
e1, e2 = sp.symbols('e1 e2')
aR1 = -s*(8*k+5)*(64*k**2*s**2 - 32*k**2 + 80*k*s**2 - 40*k + 21*s**2 - 11)/(2*(2*k+1)*(4*k+1)*(4*k+3))
aR2 = -s*(k+1)*(8*k+13)*(64*k**2*s**2 - 32*k**2 + 208*k*s**2 - 104*k + 165*s**2 - 83)/(2*(k+2)*(2*k+3)*(4*k+5)*(4*k+7))
a0 = 4*s*(k+1)*(8*k+9)
bR1 = (8*k+5)*(16*k**2*s**2 + 22*k*s**2 - 2*k + 6*s**2 - 1)/((2*k+1)*(4*k+1)*(4*k+3))
bR2 = (8*k+13)*(512*k**3*s**4 - 384*k**3*s**2 + 2240*k**2*s**4 - 1680*k**2*s**2 - 16*k**2 + 3192*k*s**4 - 2400*k*s**2 - 48*k + 1485*s**4 - 1122*s**2 - 35)/(8*(k+2)*(2*k+3)*(4*k+5)*(4*k+7))
b0 = -(8*k+9)*(8*k*s**2 + 11*s**2 - 3)/2
R1p = 4*k**2 + 5*k + sp.Rational(5,4)
R2p = 4*k**2 + 13*k + sp.Rational(41,4)
apoly = sp.cancel(R1p*aR1 + R2p*aR2 + a0)
bpoly = sp.cancel(R1p*bR1 + R2p*bR2 + b0)
print("a_poly =", sp.factor(apoly), flush=True)
print("b_poly =", sp.factor(bpoly), flush=True)
eps = sp.symbols('eps', positive=True)
def expand(expr, order):
    e = sp.cancel(expr.subs(k, 1/eps))
    ser = sp.series(e, eps, 0, order).removeO()
    return sp.expand(ser)
for name, e in (("a", apoly), ("b", bpoly)):
    ser = expand(e, 2)  # up to eps^1 = 1/k
    for p in range(-2, 2):
        c = ser.coeff(eps, p)
        print(f"{name}_poly: k^{-p} coefficient:", sp.factor(c), flush=True)
    lead = ser.coeff(eps, -2)/k**-2 if False else None
# exact remainders after the two leading orders
a2 = sp.factor(expand(apoly, 2).coeff(eps, -2)); a1 = sp.factor(expand(apoly, 2).coeff(eps, -1)); a00 = sp.factor(expand(apoly, 2).coeff(eps, 0))
b2 = sp.factor(expand(bpoly, 2).coeff(eps, -2)); b1 = sp.factor(expand(bpoly, 2).coeff(eps, -1)); b00 = sp.factor(expand(bpoly, 2).coeff(eps, 0))
rema = sp.factor(sp.cancel(apoly - a2*k**2 - a1*k - a00))
remb = sp.factor(sp.cancel(bpoly - b2*k**2 - b1*k - b00))
print("rem_a =", rema, flush=True)
print("rem_b =", remb, flush=True)
print("a1(0) =", a1.subs(s, 0), " b1(0) =", b1.subs(s, 0), flush=True)
# the epsilon (radius) corrections
print("a_R1 leading:", sp.factor(sp.limit(aR1, k, sp.oo)), " a_R2 leading:", sp.factor(sp.limit(aR2, k, sp.oo)))
print("b_R1 leading:", sp.factor(sp.limit(bR1, k, sp.oo)), " b_R2 leading:", sp.factor(sp.limit(bR2, k, sp.oo)))
print("DONE", flush=True)

#!/usr/bin/env python3
import sympy as sp, random
s, k, u, y = sp.symbols('s k u y')
def lean(e):
    e = sp.factor(e)
    return str(e).replace('**', '^')
A = {}; B = {}
A[0] = s*(8*k+5)*(64*k**2*s**2 - 32*k**2 + 80*k*s**2 - 40*k + 21*s**2 - 11)/(2*(2*k+1)*(4*k+1)*(4*k+3))
B[0] = -2*(k+1)*(64*k**2*s**2 - 16*k**2 + 64*k*s**2 - 16*k + 15*s**2 - 4)/((2*k+1)*(4*k+1)*(4*k+3))
A[1] = (64*k**2*s**2 - 16*k**2 + 96*k*s**2 - 24*k + 35*s**2 - 9)/(2*(2*k+1)*(4*k+3))
B[1] = -2*s*(k+1)*(8*k+5)/((2*k+1)*(4*k+3))
A[2] = s*(8*k+7)/(4*k+3); B[2] = -4*(k+1)/(4*k+3)
A[5] = -4*(k+1)/(4*k+5); B[5] = s*(8*k+9)/(4*k+5)
A[6] = -2*s*(k+1)*(8*k+11)/((2*k+3)*(4*k+5))
B[6] = (64*k**2*s**2 - 16*k**2 + 160*k*s**2 - 40*k + 99*s**2 - 25)/(2*(2*k+3)*(4*k+5))
A[7] = -2*(k+1)*(64*k**2*s**2 - 16*k**2 + 192*k*s**2 - 48*k + 143*s**2 - 36)/((2*k+3)*(4*k+5)*(4*k+7))
B[7] = s*(8*k+11)*(64*k**2*s**2 - 32*k**2 + 176*k*s**2 - 88*k + 117*s**2 - 59)/(2*(2*k+3)*(4*k+5)*(4*k+7))
A[8] = -s*(k+1)*(8*k+13)*(64*k**2*s**2 - 32*k**2 + 208*k*s**2 - 104*k + 165*s**2 - 83)/(2*(k+2)*(2*k+3)*(4*k+5)*(4*k+7))
B[8] = (4096*k**4*s**4 - 3072*k**4*s**2 + 256*k**4 + 24576*k**3*s**4 - 18432*k**3*s**2 + 1536*k**3 + 54656*k**2*s**4 - 41040*k**2*s**2 + 3424*k**2 + 53376*k*s**4 - 40176*k*s**2 + 3360*k + 19305*s**4 - 14586*s**2 + 1225)/(8*(k+2)*(2*k+3)*(4*k+5)*(4*k+7))
# verify the shift chain symbolically: recurrence P_{m+2} = ((2m+3) s P_{m+1} - (m+1) P_m)/(m+2) with N = 4k, P_j = A_j P3 + B_j P4
P3, P4 = sp.symbols('P3 P4')
Pj = {j: A[j]*P3 + B[j]*P4 for j in A}
Pj[3] = P3; Pj[4] = P4
N = 4*k
for m in range(0, 7):
    lhs = (m+N+2)*Pj[m+2]; rhs = (2*(N+m)+3)*s*Pj[m+1] - (N+m+1)*Pj[m]
    assert sp.simplify(lhs - rhs) == 0, m
print("shift chain verified")
for j in (0,1,2,5,6,7,8):
    print(f"A{j} := {lean(A[j])}")
    print(f"B{j} := {lean(B[j])}")
aR1 = -A[0]; aR2 = A[8]; a0 = 4*s*(k+1)*(8*k+9)
bR1 = 1 - B[0]; bR2 = B[8] - 1; b0 = -(8*k+9)*(8*k*s**2 + 11*s**2 - 3)/2
print("aR1 :=", lean(aR1)); print("aR2 :=", lean(aR2)); print("a0 :=", lean(a0))
print("bR1 :=", lean(bR1)); print("bR2 :=", lean(bR2)); print("b0 :=", lean(b0))
# check b pieces: R1 (B4 - B0) - 2 r1sq (B4 - B2) - 2 r2sq (B6 - B4) + R2 (B8 - B4) = R1 bR1 + R2 bR2 + b0
R1, R2 = sp.symbols('R1 R2')
r1sq = (2*k+sp.Rational(3,2))*(2*k+2); r2sq = (2*k+sp.Rational(5,2))*(2*k+3)
bb = R1*(1-B[0]) - 2*r1sq*(1-B[2]) - 2*r2sq*(B[6]-1) + R2*(B[8]-1)
assert sp.simplify(bb - (R1*bR1 + R2*bR2 + b0)) == 0
aa = R1*(0-A[0]) - 2*r1sq*(0-A[2]) - 2*r2sq*(A[6]-0) + R2*(A[8]-0)
assert sp.simplify(aa - (R1*aR1 + R2*aR2 + a0)) == 0
print("a,b pieces verified")
# fixed-s forms: F(k,s) with k = 1/u
print("--- fixed-s limit forms (u = 1/k) ---")
for name, F, lim in (("aR1", aR1, -4*s*(2*s**2-1)), ("aR2", aR2, -4*s*(2*s**2-1)), ("a0/k^2", a0/k**2, 32*s), ("bR1", bR1, 4*s**2), ("bR2", bR2, 4*s**2*(4*s**2-3)), ("b0/k^2", b0/k**2, -32*s**2)):
    G = sp.cancel(F.subs(k, 1/u))
    num, den = sp.fraction(G)
    print(f"{name} = ({lean(num)}) / ({lean(den)})   limit u->0: {sp.factor(sp.limit(G, u, 0))}  expected {sp.factor(lim)}")
    assert sp.simplify(sp.limit(G, u, 0) - lim) == 0
print("--- scaling limit forms (u = 1/k, s = y u) ---")
for name, F, lim in (("k*aR1", k*aR1, 4*y), ("k*aR2", k*aR2, 4*y), ("a0/k", a0/k, 32*y), ("k*bR1", k*bR1, -sp.Rational(1,2)), ("k*bR2", k*bR2, -sp.Rational(1,2)), ("b0/k", b0/k, 12)):
    G = sp.cancel(F.subs({k: 1/u, s: y*u}))
    num, den = sp.fraction(G)
    print(f"{name} = ({lean(num)}) / ({lean(den)})   limit u->0: {sp.factor(sp.limit(G, u, 0))}  expected {lim}")
    assert sp.simplify(sp.limit(G, u, 0) - lim) == 0
print("DONE")

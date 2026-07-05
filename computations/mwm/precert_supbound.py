#!/usr/bin/env python3
"""Pre-certify the analytic weak sup bound R(1/2,c,0) <= 4/(3c) for c >= 2.

R(c) = I1(c) - I2(c),
I1 = c * int_0^{log2} 2 sinh^2(z/2) csch^2(cz/2) dz
I2 = c * int_{log2}^inf (1-e^-z) * (1/2) csch^2(cz/2) dz

Claims to check:
  (A) pointwise: sinh(c z/2) >= c sinh(z/2) cosh(z/2)  for c>=2, z>0
  (B) hence I1(c) <= (2/c) * int_0^{log2} sech^2(z/2) dz = 4/(3c)
  (C) R(c) <= I1(c) (I2 >= 0)
  (D) margins: 4/(3c) - R(c) on a grid; and 4/(3c) < 1/4 iff c > 16/3
"""
from mpmath import mp, mpf, sinh, cosh, sech, csch, exp, log, quad, inf

mp.dps = 30
L2 = log(2)

def I1(c):
    return c * quad(lambda z: 2 * sinh(z/2)**2 * csch(c*z/2)**2, [0, L2])

def I2(c):
    return c * quad(lambda z: (1 - exp(-z)) * csch(c*z/2)**2 / 2, [L2, inf])

def R(c):
    return I1(c) - I2(c)

# (A) pointwise inequality
worstA = None
for ci in [2, 2.1, 2.5, 3, 4, 5, 5.33, 6, 8, 12]:
    for zi in [1e-6, 0.01, 0.1, 0.3, 0.5, 0.693, 1.0, 2.0]:
        c, z = mpf(ci), mpf(zi)
        lhs = sinh(c*z/2)
        rhs = c * sinh(z/2) * cosh(z/2)
        d = lhs - rhs
        if worstA is None or d < worstA[0]:
            worstA = (d, ci, zi)
print("(A) min(lhs-rhs) =", worstA)

# (B),(C),(D)
print(f"{'c':>6} {'I1':>12} {'4/(3c)':>10} {'I1<=bd':>7} {'R':>12} {'bd-R':>10}")
maxR = (mpf(0), 0)
for ci in [2 + k*mpf('0.05') for k in range(0, 81)] + [mpf(16)/3, 6, 8, 10]:
    c = mpf(ci)
    i1, i2 = I1(c), I2(c)
    bd = mpf(4)/(3*c)
    r = i1 - i2
    if r > maxR[0]:
        maxR = (r, c)
    assert i1 <= bd + mpf('1e-20'), (c, i1, bd)
    assert i2 >= 0
for ci in [2, 2.25, 2.5, 2.53, 2.75, 3, 4, mpf(16)/3, 6, 8]:
    c = mpf(ci)
    i1, r, bd = I1(c), R(c), mpf(4)/(3*c)
    print(f"{float(c):6.3f} {float(i1):12.8f} {float(bd):10.6f} {str(i1<=bd):>7} {float(r):12.8f} {float(bd-r):10.6f}")
print("max R on grid:", float(maxR[0]), "at c =", float(maxR[1]))
print("sharp check: 4/(3c) < 1/4 iff c > 16/3 =", float(mpf(16)/3))
print("consumer check: 2/3 =", float(mpf(2)/3), "<= 0.79 budget:", mpf(2)/3 < mpf('0.79'))
print("ALL ASSERTS PASSED")

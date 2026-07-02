import sympy as sp
sig, z, r, b = sp.symbols('sigma z r b')

# CLAIM: 3-cycle of z^2+b with trace sigma has b = -(sigma^2+sigma+2),
# and cycle points are roots of cubic Q(z) below.
bexpr = -(sig**2 + sig + 2)
Q = z**3 - sig*z**2 - (sig**2 + 2*sig + 3)*z + (sig**3 + 2*sig**2 + 3*sig + 1)

# Verify: if r is a root of Q, then f^3(r) = r with f(z)=z^2+bexpr, and f(r)!=r generically,
# and the three roots form one 3-cycle. Check f permutes the roots of Q.
f = lambda w: w**2 + bexpr
# Check that Q divides Q(f(z))/(leading) i.e. roots map to roots: reduce f(z) mod Q and see cycle
# Simplest: pick the three roots symbolically? Instead verify f^3(z) - z is divisible by Q.
f3 = f(f(f(z)))
rem = sp.rem(sp.expand(f3 - z), Q, z)
print("f^3(z)-z  mod Q  =", sp.simplify(rem))   # expect 0 => every root of Q is period-<=3
# Also f(z)-z should NOT be divisible (genuine period 3): check gcd
g = sp.gcd(sp.Poly(f(z)-z, z), sp.Poly(Q, z))
print("gcd(f(z)-z, Q) =", g)

# Verify trace: sum of roots of Q = sigma  (Vieta) -> coefficient check
print("sum of roots (Vieta) =", sp.Poly(Q, z).all_coeffs()[1] * -1)

# Does the marked-point curve P(sigma,r)=0 have a rational section sigma(r)?
P = sp.expand(Q.subs(z, r))
Pfac = sp.factor(P, extension=[sp.I])
print("\nP(sigma,r) factor over Q(i):", Pfac)
# as polynomial in sigma over Q(r): factor
Psig = sp.Poly(P, sig)
print("P as poly in sigma, factor_list over QQ(r):")
print(sp.factor_list(P, sig))

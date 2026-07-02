import sympy as sp
sig, r, t = sp.symbols('sigma r t')
P = r**3 - r**2*sig - r*sig**2 - 2*r*sig - 3*r + sig**3 + 2*sig**2 + 3*sig + 1
print("total degree:", sp.Poly(P, sig, r).total_degree())
# singular point: P = dP/dsig = dP/dr = 0
sol = sp.solve([P, sp.diff(P,sig), sp.diff(P,r)], [sig, r], dict=True)
print("singular points (affine):", sol)
# also check at infinity: homogenize
X,Y,Z = sp.symbols('X Y Z')
Ph = sp.expand(P.subs({sig:X/Z, r:Y/Z})*Z**3)
Ph = sp.simplify(Ph)
print("homogenized:", Ph)
# leading form (Z=0):
lead = Ph.subs(Z,0)
print("leading form (points at infinity):", sp.factor(lead))

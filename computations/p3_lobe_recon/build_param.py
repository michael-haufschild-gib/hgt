import sympy as sp
sig, r, t = sp.symbols('sigma r t')
P = r**3 - r**2*sig - r*sig**2 - 2*r*sig - 3*r + sig**3 + 2*sig**2 + 3*sig + 1
# line through singular pt at infinity [1:1:0]:  r = sigma + t
Psub = sp.expand(P.subs(r, sig + t))
Ppoly = sp.Poly(Psub, sig)
print("P(sigma, sigma+t) as poly in sigma:", Ppoly)
print("degree in sigma:", Ppoly.degree())
coeffs = Ppoly.all_coeffs()
print("coeffs (high->low):", coeffs)
# linear: c1*sigma + c0 = 0 -> sigma = -c0/c1
if Ppoly.degree()==1:
    c1, c0 = coeffs
    sigt = sp.simplify(-c0/c1)
    rt = sp.simplify(sigt + t)
    bt = sp.simplify(-(sigt**2 + sigt + 2))
    print("\nsigma(t) =", sigt)
    print("r(t)     =", rt)
    print("b(t)     =", bt)
    # VERIFY: r(t) is a genuine period-3 point of z^2+b(t)
    f = lambda w,c: w**2 + c
    lhs = sp.simplify(f(f(f(rt,bt),bt),bt) - rt)
    print("\nverify f^3(r)-r =", lhs)
    per1 = sp.simplify(f(rt,bt)-rt)
    print("f(r)-r (should be nonzero) =", per1)
    # save the parameterization
    with open('param.txt','w') as fh:
        fh.write(f"sigma(t)={sigt}\nr(t)={rt}\nb(t)={bt}\n")

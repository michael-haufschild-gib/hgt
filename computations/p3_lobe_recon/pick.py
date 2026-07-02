import sympy as sp, math
t=sp.symbols('t')
r_t=(t**3-2*t**2+3*t-1)/(2*t*(t-1)); b_t=-(t**6-2*t**5+4*t**4-8*t**3+9*t**2-4*t+1)/(4*t**2*(t-1)**2)
I=sp.I
tests=[I,2*I,3*I,I/2,3*I/2,1+I,1+2*I,2+I,1+3*I,sp.Rational(1,2)+I,sp.Rational(3,2)+I,-I+1,I/3,2*I/3,sp.Rational(1,2)+2*I,1-I]
for tv in tests:
    bv=sp.nsimplify(sp.simplify(b_t.subs(t,tv))); rv=sp.nsimplify(sp.simplify(r_t.subs(t,tv)))
    f=lambda w: sp.expand(w**2+bv); cyc=[rv,sp.simplify(f(rv))]; cyc.append(sp.simplify(f(cyc[1])))
    bc=complex(bv); rr=abs(bc); ang=math.degrees(math.atan2(bc.imag,bc.real))
    ds=[abs(complex(g)-bc) for g in cyc]; mind=min(ds); w=ds.index(mind)
    tag = "LOBE" if (1.9<rr<2.6 and 60<abs(ang)<160 and mind<=1.0) else ""
    print(f"t={tv}: b={bv} |b|={rr:.3f} arg={ang:.1f} y={cyc[w]} |y-b|={mind:.3f} {tag}")

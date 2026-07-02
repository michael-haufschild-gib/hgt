import sympy as sp
I=sp.I
# --- Instance 1: period-3 at arg 111.8 (via general theorem #40, n=3) ---
b1=sp.Rational(-1,4)+sp.Rational(5,8)*I; y1=sp.Rational(-1,4)+sp.Rational(3,4)*I
f=lambda w,c: sp.expand(w**2+c)
p=sp.expand(f(y1,b1)); q=sp.expand(f(p,b1)); z3=sp.expand(f(q,b1))
print("INST1 b=",b1," y=",y1)
print("  f(y)=",p,"  f2=",q,"  f3=",sp.simplify(z3),"  f3==y:",sp.simplify(z3-y1)==0)
print("  distinct 3:",len({y1,p,q})==3, "  |y-b|^2=",sp.simplify(sp.Abs(y1-b1)**2))
print("  |b|^2=",sp.simplify(sp.Abs(b1)**2),"=",float(sp.Abs(b1)))
# --- Instance 2: P2 ring at arg 126.9, gamma=-8/5+4i/5 ---
g=sp.Rational(-8,5)+sp.Rational(4,5)*I
b2=sp.expand(-(g**2+g+1))
print("\nINST2 gamma=",g," b=-(g^2+g+1)=",b2)
print("  g^2+g+b+1==0:",sp.simplify(g**2+g+b2+1)==0)
print("  g-b=",sp.expand(g-b2)," =(g+1)^2:",sp.simplify((g-b2)-(g+1)**2)==0)
print("  |g-b|^2=",sp.simplify(sp.Abs(g-b2)**2))
print("  |b|^2=",sp.simplify(sp.Abs(b2)**2),"=",float(sp.Abs(b2)),"arg=",float(sp.arg(b2))*180/sp.pi.evalf())
# --- radial bracket: viable partner = 2*b2 (colinear), |2b2|^2 vs (2+sqrt2)^2 ---
bv=sp.expand(2*b2)
print("\nRADIAL viable partner bv=2*b2=",bv," |bv|^2=",sp.simplify(sp.Abs(bv)**2),"=",float(sp.Abs(bv)))
print("  (2+sqrt2)^2=",float((2+sp.sqrt(2))**2)," need |bv|>2+sqrt2:",float(sp.Abs(bv))>float(2+sp.sqrt(2)))
print("  colinear bv.im*b2.re==bv.re*b2.im:", sp.im(bv)*sp.re(b2)==sp.re(bv)*sp.im(b2))

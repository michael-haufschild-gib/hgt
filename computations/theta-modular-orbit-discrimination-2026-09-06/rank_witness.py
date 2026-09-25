"""Exact candidate for the cubic test y²(y-200). Runpod only, not a proof oracle."""
from pathlib import Path
import json,math,time
from fractions import Fraction as Q
import sympy as sy
ROOT=Path(__file__).resolve().parent
def conv(a,b,n):return sy.expand(sum(a[k]*b[n-k] for k in range(n+1)))
if __name__=='__main__':
    start=time.monotonic();X=sy.symbols('X');s=[sy.Integer(0)];a=[X];w=[sy.Integer(0)];h=[sy.Integer(1)]
    for n in range(14):
        ss=conv(s,s,n);sw=conv(s,w,n);aw=conv(a,w,n)
        sn=sy.expand(((3 if n==0 else 0)-ss/3-3*a[n]/4)/(n+1))
        an=sy.expand(-2*aw/(n+1))
        wn=sy.expand(((2 if n==0 else 0)+a[n]/2+2*ss/9-2*sw/3)/(n+1))
        hn=sy.expand(-conv(s,h,n)/(6*(n+1)))
        s.append(sn);a.append(an);w.append(wn);h.append(hn)
    f=[sy.expand((sy.factorial(n+2)*h[n+2]-sy.factorial(n)*h[n]/4)/2) for n in range(13)]
    pp={m:sy.expand(sum((-1)**j*math.comb(m,j)*f[j]*f[m-j] for j in range(m+1))) for m in (8,10,12)}
    P=sy.Poly(pp[12]+400*pp[10]+40000*pp[8],X)
    t=sy.symbols('t');translated=sy.Poly(-P.as_expr().subs(X,sy.Rational(191,10)+sy.Rational(9,10)*t),t)
    n=translated.degree();coeff=[Q(str(translated.nth(i))) for i in range(n+1)]
    bs=[sum(coeff[i]*Q(math.comb(j,i),math.comb(n,i)) for i in range(j+1)) for j in range(n+1)]
    out=dict(polynomial=str(P.as_expr()),coefficients=[str(P.nth(i)) for i in range(P.degree()+1)],
        negative_bernstein_coefficients=[str(c) for c in bs],all_positive=all(c>0 for c in bs),
        source_even_jets=[str(f[n]) for n in range(0,13,2)],seconds=time.monotonic()-start)
    (ROOT/'rank_witness.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

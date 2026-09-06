"""Exact candidate search for B1. Runpod only; symbolic identity still requires Lean proof."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json,time,itertools,math
from fractions import Fraction as Q
import sympy as sy
ROOT=Path(__file__).resolve().parent
if __name__=='__main__':
    start=time.monotonic();S,A,W=sy.symbols('S A W');vs=(S,A,W)
    raw=json.loads((ROOT/'jet_polynomials.json').read_text())
    f=[sy.Poly.from_dict({tuple(t['exponents']):sy.Rational(t['coefficient']) for t in rows},vs) for rows in raw]
    p0=f[0]**2;p2=2*(f[0]*f[2]-f[1]**2)
    p4=2*f[0]*f[4]-8*f[1]*f[3]+6*f[2]**2
    p6=2*f[0]*f[6]-12*f[1]*f[5]+30*f[2]*f[4]-20*f[3]**2
    p8=2*f[0]*f[8]-16*f[1]*f[7]+56*f[2]*f[6]-112*f[3]*f[5]+70*f[4]**2
    P=p0*p4*p8-p0*p6**2-p2**2*p8+2*p2*p4*p6-p4**3
    (ROOT/'d1_polynomial.json').write_text(json.dumps([dict(exponents=list(e),coefficient=str(c)) for e,c in P.terms()],indent=2)+'\n')
    # Tensor basis x=-S in[0,1], y=(A-17)/3, z=5W/6.
    terms={e:Q(int(c.p),int(c.q)) for e,c in P.terms()}
    affine=[(Q(0),Q(-1)),(Q(17),Q(3)),(Q(0),Q(6,5))]
    for axis,(a,b) in enumerate(affine):
        new={}
        for e,c in terms.items():
            for k in range(e[axis]+1):
                ee=list(e);ee[axis]=k;ee=tuple(ee)
                val=c*math.comb(e[axis],k)*a**(e[axis]-k)*b**k
                new[ee]=new.get(ee,Q(0))+val
        terms={e:c for e,c in new.items() if c}
    deg=[max(e[i] for e in terms) for i in range(3)]
    # Coefficients in binomial-normalized tensor Bernstein basis.
    bern=terms
    for axis,n in enumerate(deg):
        new={}
        for e,c in bern.items():
            for j in range(e[axis],n+1):
                ee=list(e);ee[axis]=j;ee=tuple(ee)
                val=c*Q(math.comb(j,e[axis]),math.comb(n,e[axis]))
                new[ee]=new.get(ee,Q(0))+val
        bern=new
    minimum=min(bern.values());negative=[(e,c) for e,c in bern.items() if c<0]
    out=dict(degrees=deg,polynomial_terms=len(P.terms()),coefficient_count=len(bern),negative_count=len(negative),minimum=str(minimum),seconds=time.monotonic()-start,
             coefficients=[dict(index=list(e),value=str(c)) for e,c in sorted(bern.items())])
    (ROOT/'bernstein.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='coefficients'},indent=2))

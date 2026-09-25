"""Inspect exact candidate certificate compression, on Runpod."""
from pathlib import Path
import json,itertools,math,time
from fractions import Fraction as Q
ROOT=Path(__file__).resolve().parent

def expand(terms,axis,a,b):
    out={}
    for e,c in terms.items():
        for k in range(e[axis]+1):
            val=c*math.comb(e[axis],k)*a**(e[axis]-k)*b**k
            if not val:continue
            f=list(e);f[axis]=k;f=tuple(f);out[f]=out.get(f,Q(0))+val
    return {e:c for e,c in out.items() if c}

def bernstein(terms,axis,n):
    out={}
    for e,c in terms.items():
        for j in range(e[axis],n+1):
            f=list(e);f[axis]=j;f=tuple(f)
            out[f]=out.get(f,Q(0))+c*Q(math.comb(j,e[axis]),math.comb(n,e[axis]))
    return {e:c for e,c in out.items() if c}

if __name__=='__main__':
    start=time.monotonic();original={tuple(r['exponents']):Q(r['coefficient']) for r in json.loads((ROOT/'d1_polynomial.json').read_text())}
    rows=[];best=None
    for bits in itertools.product((0,1),repeat=3):
        bounds=[(Q(0),Q(-1)),(Q(17),Q(3)),(Q(0),Q(6,5))]
        terms=original
        for i,(a,b) in enumerate(bounds):terms=expand(terms,i,a+(b if bits[i] else 0),-b if bits[i] else b)
        degrees=[max(e[i] for e in terms) for i in range(3)]
        for mask in range(8):
            bs=terms
            for i in range(3):
                if mask>>i&1:bs=bernstein(bs,i,degrees[i])
            neg=sum(c<0 for c in bs.values());row=dict(corner=bits,bernstein_axes=[i for i in range(3) if mask>>i&1],terms=len(bs),negative=neg,minimum=str(min(bs.values())))
            rows.append(row)
            if not neg and (best is None or len(bs)<best[0]):best=(len(bs),row,bs)
    out=dict(rows=rows,best=best[1] if best else None,seconds=time.monotonic()-start)
    (ROOT/'structure.json').write_text(json.dumps(out,indent=2)+'\n')
    if best:(ROOT/'compressed_certificate.json').write_text(json.dumps(dict(**best[1],coefficients=[dict(index=list(e),value=str(c)) for e,c in sorted(best[2].items())]),indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))

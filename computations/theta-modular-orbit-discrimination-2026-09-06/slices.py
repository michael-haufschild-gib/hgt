"""Search compact symbolic B1 certificates, on Runpod. Outputs are proof candidates."""
from pathlib import Path
from fractions import Fraction as Q
import json, math, time
from structure import expand, bernstein
ROOT=Path(__file__).resolve().parent
if __name__=='__main__':
    start=time.monotonic()
    original={tuple(r['exponents']):Q(r['coefficient']) for r in json.loads((ROOT/'d1_polynomial.json').read_text())}
    shifted=expand(expand(expand(original,0,Q(0),Q(-1)),1,Q(17),Q(1)),2,Q(0),Q(6,5))
    rows=[]
    for j in range(13):
        terms={e:c for e,c in shifted.items() if e[1]==j}
        degrees=[max(e[i] for e in terms) for i in range(3)]
        candidates=[]
        for mask in range(4):
            for dn in range(7):
                bs=terms
                ns=[degrees[0]+dn,degrees[2]+dn]
                for k,i in enumerate((0,2)):
                    if mask>>k&1:bs=bernstein(bs,i,ns[k])
                if min(bs.values())>=0:
                    candidates.append((len(bs),mask,ns,bs));break
        if not candidates:
            raise RuntimeError('no positive slice %s'%j)
        _,mask,ns,bs=min(candidates,key=lambda c:c[0])
        rows.append(dict(j=j,degrees=degrees,mask=mask,bernstein_degrees=ns,
            original=[dict(index=list(e),value=str(c)) for e,c in sorted(terms.items())],
            coefficients=[dict(index=list(e),value=str(c)) for e,c in sorted(bs.items())]))
    out=dict(slices=rows,seconds=time.monotonic()-start)
    (ROOT/'slices.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(seconds=out['seconds'],slices=[dict(j=r['j'],degrees=r['degrees'],mask=r['mask'],n=r['bernstein_degrees'],terms=len(r['coefficients'])) for r in rows]),indent=2))

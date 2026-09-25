"""Runpod-only guidance: no certified tail bound or interval positivity claim."""
import json
import math
import os
import time
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from pathlib import Path
import mpmath as mp


def polynomials():
    p = [[Fraction(0), Fraction(-6), Fraction(4)]]
    for _ in range(12):
        old = p[-1]
        new = [Fraction(0)] * (len(old)+1)
        for i, c in enumerate(old):
            new[i] += (Fraction(1,2)+2*i)*c
            new[i+1] -= 2*c
        p.append(new)
    return p


def normalized(x, atoms):
    q = mp.pi*mp.exp(2*x)
    coeff = polynomials()
    pp = [[mp.mpf(c.numerator)/c.denominator for c in cs] for cs in coeff]
    leading = 4*q*q-6*q
    d = [mp.fsum(mp.exp(-(n*n-1)*q)*mp.polyval(list(reversed(cs)),n*n*q)
                 for n in range(1,atoms+1))/leading for cs in pp]
    moments = [(-1)**k*mp.fsum((-1)**i*math.comb(2*k,i)*d[i]*d[2*k-i]
                              for i in range(2*k+1))/q**k for k in range(7)]
    head = mp.matrix([[moments[i+j] for j in range(3)] for i in range(3)])
    border = mp.matrix(moments[3:6])
    schur = moments[6]-(border.T*mp.lu_solve(head,border))[0]
    correction = (3*d[0]**2+2*x*d[0]*d[1])/q**6
    return q, d[0], schur, correction, mp.det(head)


def worker(job):
    i, count, canonical = job
    mp.mp.dps = 100
    x = mp.mpf(8)/95+(mp.mpf(6)/5-mp.mpf(8)/95)*i/count
    rows=[]
    for atoms in (12,18):
        q,p0,s,g,h=normalized(x,atoms)
        rows.append({'atoms':atoms,'q':mp.nstr(q,80),'schur':mp.nstr(s,80),
                     'correction':mp.nstr(g,80),'head_det':mp.nstr(h,80),
                     'corrected':{c:mp.nstr(s+mp.mpf(c)*g,80)
                                  for c in ('1000000000000',canonical,'3000000000000')}})
    return {'index':i,'x':mp.nstr(x,80),'truncations':rows}


if __name__ == '__main__':
    started=time.monotonic()
    mp.mp.dps=100
    q,p0,s,g,h=normalized(mp.mpf(0),18)
    canonical=mp.nstr((abs(s*q**6)+p0**2)/p0**2,90)
    workers=min(16,os.cpu_count() or 1)
    with ProcessPoolExecutor(max_workers=workers) as pool:
        rows=list(pool.map(worker,[(i,64,canonical) for i in range(65)],chunksize=1))
    summary={c:min((mp.mpf(r['truncations'][-1]['corrected'][c]),r['x']) for r in rows)
             for c in ('1000000000000',canonical,'3000000000000')}
    result={'scope':'Guidance only. Finite atom sums and finitely many centers; no certified tails.',
            'cpu_count':os.cpu_count(),'workers':workers,'precision_decimal_digits':100,
            'canonical_coefficient_18_atoms':canonical,
            'minima':{c:{'value':mp.nstr(v,80),'x':x} for c,(v,x) in summary.items()},
            'rows':rows,'seconds':time.monotonic()-started}
    Path('results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2),flush=True)

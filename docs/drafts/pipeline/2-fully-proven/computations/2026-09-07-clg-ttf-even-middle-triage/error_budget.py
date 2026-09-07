"""Runpod-only numerical triage of the corpus's complete finite matrix error."""
import itertools
import json
import math
import os
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import mpmath as mp
from scan import polynomials


def worker(i):
    mp.mp.dps=100
    x=mp.mpf(8)/95+(mp.mpf(6)/5-mp.mpf(8)/95)*i/64
    q=mp.pi*mp.exp(2*x)
    p=[[mp.mpf(c.numerator)/c.denominator for c in cs] for cs in polynomials()]
    base=4*q*q-6*q
    first=[mp.polyval(list(reversed(cs)),q)/base for cs in p]
    second=[mp.exp(-3*q)*mp.polyval(list(reversed(cs)),4*q)/base for cs in p]
    two=[a+b for a,b in zip(first,second)]
    relative=[]
    for n in range(13):
        relative.append(second[n]-mp.fsum(math.comb(n,j)*first[j]*relative[n-j]
                                         for j in range(1,n+1)))
    partition=relative[:]
    partition[0]+=1
    delta=mp.exp(-8*(q-mp.mpf(49)/20))/1000000
    deep=[(1 if n<=10 else mp.mpf(5)/4)*(16*q)**n*delta for n in range(13)]
    reflected_error=[mp.fsum(math.comb(n,j)*(abs(partition[j])*deep[n-j]+
                      deep[j]*abs(partition[n-j])+deep[j]*deep[n-j])
                      for j in range(n+1)) for n in range(13)]
    first_reflected=[mp.fsum((-1)**j*math.comb(n,j)*first[j]*first[n-j]
                            for j in range(n+1)) for n in range(13)]
    entry_error=[mp.fsum(math.comb(2*k,j)*abs(first_reflected[j])*reflected_error[2*k-j]
                        for j in range(2*k+1))/(32*q)**k for k in range(7)]
    moments=[(-1)**k*mp.fsum((-1)**j*math.comb(2*k,j)*two[j]*two[2*k-j]
                            for j in range(2*k+1))/(32*q)**k for k in range(7)]
    source_error=[mp.fsum(math.comb(n,j)*abs(first[j])*deep[n-j] for j in range(n+1))
                  for n in range(2)]
    e0,e1=source_error
    correction_error=3*(2*abs(two[0])*e0+e0**2)+2*abs(x)*(
        abs(two[0])*e1+abs(two[1])*e0+e0*e1)
    correction=(3*two[0]**2+2*x*two[0]*two[1])/(32*q)**6
    lower=mp.matrix([[moments[j+k] for k in range(4)] for j in range(4)])
    lower[3,3]+=min(mp.mpf(10)**12*correction,3*mp.mpf(10)**12*correction)
    error=mp.matrix([[entry_error[j+k] for k in range(4)] for j in range(4)])
    error[3,3]+=3*mp.mpf(10)**12*correction_error/(32*q)**6
    records=[]
    for tail in itertools.product((-1,1),repeat=3):
        signs=(1,)+tail
        a=mp.matrix([[lower[j,k]-signs[j]*error[j,k]*signs[k] for k in range(4)]
                     for j in range(4)])
        minors=[mp.det(mp.matrix([[a[j,k] for k in range(n)] for j in range(n)]))
                for n in range(1,5)]
        records.append({'signs':signs,'leading_minors':[mp.nstr(d,80) for d in minors],
                        'all_positive':all(d>0 for d in minors)})
    return {'index':i,'x':mp.nstr(x,80),'q':mp.nstr(q,80),'sign_cases':records,
            'all_positive':all(r['all_positive'] for r in records)}


if __name__=='__main__':
    started=time.monotonic()
    workers=min(16,os.cpu_count() or 1)
    with ProcessPoolExecutor(max_workers=workers) as pool: rows=list(pool.map(worker,range(65)))
    failures=[{'x':r['x'],'q':r['q']} for r in rows if not r['all_positive']]
    result={'scope':'Guidance only; no rigorous floating-point or between-center bounds.',
            'workers':workers,'precision_decimal_digits':100,
            'failed_centers':failures,'rows':rows,'seconds':time.monotonic()-started}
    Path('error-budget-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2),flush=True)

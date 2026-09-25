"""Independent small witness audit and exploratory smoothing-order profile. Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json,time
import numpy as np
import mpmath as mp
ROOT=Path(__file__).resolve().parent

def mu(n):
    sign=1; p=2
    while p*p<=n:
        if n%p==0:
            sign=-sign; n//=p
            if n%p==0:return 0
        p+=1
    return -sign if n>1 else sign

def exact(M,weights,dps):
    mp.mp.dps=dps
    defect=[mp.mpf(0)]+[mp.log(mp.factorial(q))-sum(q//d for d in range(1,q+1))+2*mp.euler*q for q in range(1,M)]
    w=weights(M)
    channels=[mu(d)*mp.fsum(w[k-1]*defect[k//d] for k in range(d,M)) for d in range(1,M+1)]
    s=mp.fsum(channels); q=mp.fsum(c*c for c in channels)
    return dict(source=mp.nstr(s,75),diagonal=mp.nstr(q,75),ratio=mp.nstr(s*s/q,75),
                margin=mp.nstr(q-s*s,75),channels=[mp.nstr(c,75) for c in channels])

if __name__=='__main__':
    start=time.monotonic()
    cases=[('flat',lambda M:[mp.mpf(1)]*(M-1)),
           ('strict_decrease',lambda M:[1-mp.mpf(k-1)/100 for k in range(1,M)]),
           ('square_root',lambda M:[mp.sqrt(k+1)-mp.sqrt(k) for k in range(1,M)])]
    audits=[dict(name=name,dps=dps,M=7,**exact(7,f,dps)) for name,f in cases for dps in (60,100)]
    z=np.load('/root/rh-mobius-divisor-coordination-20260906/source.npz'); D=z['defect'][:513];D[0]=0;MU=z['mu'][:513]
    k=np.arange(1,512)
    orders=[]
    for a in (-.5,0,.25,.5,.75,1,1.25,2):
        if a==0:w=np.log1p(1/k)
        else:w=k**a*np.expm1(a*np.log1p(1/k))/a
        v=np.empty((512,511))
        for d in range(1,513):v[d-1]=MU[d]*np.cumsum(w*D[k//d])
        source=v.sum(axis=0);diagonal=(v*v).sum(axis=0);ratio=source*source/diagonal
        bad=np.flatnonzero(ratio>1+1e-9)
        orders.append(dict(alpha=a,first_failure_M=int(bad[0]+2) if len(bad) else None,
                           max_ratio_excluding_M2=float(ratio[1:].max()),
                           max_M=int(np.argmax(ratio[1:])+3),M7_ratio=float(ratio[5])))
    result=dict(audits=audits,orders=orders,seconds=time.monotonic()-start,
                interpretation='The order scan is a descriptive follow-up, not a weakened replacement for DW1. No global order interval is claimed.')
    (ROOT/'followup.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(audits=[{k:r[k] for k in ('name','dps','M','ratio','margin')} for r in audits],orders=orders,seconds=result['seconds']),indent=2))

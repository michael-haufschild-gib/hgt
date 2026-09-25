"""PH1 entire flat-prefix dual cone; Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json,time,multiprocessing as pool
import numpy as np
import mpmath as mp
from followup import mu
ROOT=Path(__file__).resolve().parent

def scan(M):
    # Exact finite quotient-block channel formula, evaluated in floating point.
    d=np.arange(1,M+1);q=M//d
    c=MU[d]*(np.sqrt(d)*ABEL[q-1]+D[q]*(M-d*q)/(np.sqrt(M)+np.sqrt(d*q)))
    s=c.sum()
    # Jumps in sum_d C_d mu(d) D(floor(k/d)) at every product d*q.
    jumps=np.zeros(M)
    for di in range(1,M):
        if MU[di]:jumps[di:M:di]+=c[di-1]*MU[di]*DD[1:(M-1)//di+1]
    residual=np.cumsum(jumps)[1:]-s*PSI[1:M]
    prefix=np.cumsum(residual)
    index=int(np.argmin(prefix))
    return dict(M=M,min_margin=float(prefix[index]),t=index+1,
                source=float(s),bad_count=int(np.sum(prefix< -1e-8)),
                end_margin=float(prefix[-1]))

def audit(M,t,dps):
    mp.mp.dps=dps
    defect=[mp.mpf(0)]+[mp.log(mp.factorial(k))-sum(k//d for d in range(1,k+1))+2*mp.euler*k for k in range(1,M)]
    c=[mu(d)*mp.fsum((mp.sqrt(k+1)-mp.sqrt(k))*defect[k//d] for k in range(d,M)) for d in range(1,M+1)]
    f=[mu(d)*mp.fsum(defect[k//d] for k in range(d,t+1)) for d in range(1,M+1)]
    b=mp.fsum(x*y for x,y in zip(c,f))-mp.fsum(c)*mp.fsum(f)
    return dict(M=M,t=t,dps=dps,margin=mp.nstr(b,75))

if __name__=='__main__':
    start=time.monotonic();z=np.load('/root/rh-mobius-divisor-coordination-20260906/source.npz')
    D=z['defect'];D[0]=0;MU=z['mu'];ABEL=z['abel'];DD=np.diff(D,prepend=0)
    # Archive psi stores psi(k); recover psiDefect by the exact corpus identity.
    k=np.arange(len(D));PSI=z['psi']-k+2*float(mp.euler);PSI[0]=0
    endpoints=list(range(2,513))+[1024,2048,4096,8192,16384,32768,65536]
    with pool.get_context('fork').Pool(8) as p:rows=list(p.imap(scan,endpoints,chunksize=4))
    bad=[r for r in rows if r['bad_count']];chosen=([bad[0],min(bad,key=lambda r:r['min_margin'])] if bad else [min(rows[1:],key=lambda r:r['min_margin'])])
    # High precision direct arithmetic at small endpoints; retain larger failures for a separate audit.
    audits=[audit(r['M'],r['t'],dps) for r in chosen if r['M']<=512 for dps in (60,100)]
    out=dict(rows=rows,first_failure=bad[0] if bad else None,worst=min(rows,key=lambda r:r['min_margin']),audits=audits,seconds=time.monotonic()-start)
    (ROOT/'prefix_cross.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))

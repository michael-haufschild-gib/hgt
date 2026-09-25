"""GH1 mixed geometric/half-order sign falsification; Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
import json,time,multiprocessing as pool
from pathlib import Path
import numpy as np
import mpmath as mp
from followup import mu
ROOT=Path(__file__).resolve().parent

def scan(M):
    k=np.arange(1,M); d=np.arange(1,M+1)
    v=MU[d,None]*D[k[None,:]//d[:,None]]
    w=1/(np.sqrt(k+1)+np.sqrt(k)); c=v@w; s=c.sum()
    residual=c@v-s*v.sum(axis=0)
    # Divide by q, a positive common factor, to retain fast-kernel signs.
    geo=np.exp(-(U[:,None]/M)*(k[None,:]-1))
    b=geo@residual
    denom=np.linalg.norm(c)*np.linalg.norm(v@geo.T,axis=0)
    scaled=b/np.maximum(denom,1e-300)
    j=int(np.argmin(scaled))
    return dict(M=M,u=float(U[j]),q=float(np.exp(-U[j]/M)),scaled=float(scaled[j]),
                margin_div_q=float(b[j]),bad_count=int(np.sum(scaled< -1e-9)))

def audit(M,q,dps):
    mp.mp.dps=dps;q=mp.mpf(q)
    D=[mp.mpf(0)]+[mp.log(mp.factorial(k))-sum(k//d for d in range(1,k+1))+2*mp.euler*k for k in range(1,M)]
    a=[];b=[]
    for d in range(1,M+1):
        a.append(mu(d)*mp.fsum((mp.sqrt(k+1)-mp.sqrt(k))*D[k//d] for k in range(d,M)))
        b.append(mu(d)*mp.fsum(q**k*D[k//d] for k in range(d,M)))
    cross=mp.fsum(x*y for x,y in zip(a,b))-mp.fsum(a)*mp.fsum(b)
    return dict(M=M,q=str(q),dps=dps,margin=mp.nstr(cross,75),
                normalized=mp.nstr(cross/mp.sqrt(mp.fsum(x*x for x in a)*mp.fsum(y*y for y in b)),75))

if __name__=='__main__':
    start=time.monotonic();z=np.load('/root/rh-mobius-divisor-coordination-20260906/source.npz')
    D=z['defect'][:513];D[0]=0;MU=z['mu'][:513];U=np.logspace(-3,4,113)
    with pool.get_context('fork').Pool(8) as p:rows=list(p.imap(scan,range(2,513),chunksize=4))
    bad=[r for r in rows if r['scaled'] < -1e-9];worst=min(rows,key=lambda r:r['scaled'])
    # Freeze an explicit rational q close to the optimizer, not a low-precision transcendental q.
    candidates=[worst]+([bad[0]] if bad else [])
    audits=[audit(r['M'],str(round(r['q'],8)),dps) for r in candidates for dps in (60,100)]
    out=dict(rows=rows,worst=worst,first_failure=bad[0] if bad else None,audits=audits,seconds=time.monotonic()-start)
    (ROOT/'geometric_cross.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))

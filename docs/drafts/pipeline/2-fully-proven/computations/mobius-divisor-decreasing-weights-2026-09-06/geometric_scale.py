"""GH1 quotient-event evaluation at fixed larger scales; Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
import json,time,multiprocessing as pool
from pathlib import Path
import numpy as np
from geometric_cross import audit
ROOT=Path(__file__).resolve().parent

def scan(M):
    d=np.arange(1,M+1);q=M//d
    c=MU[d]*(np.sqrt(d)*ABEL[q-1]+D[q]*(M-d*q)/(np.sqrt(M)+np.sqrt(d*q)))
    s=c.sum();jumps=np.zeros(M)
    for di in range(1,M):
        if MU[di]:jumps[di:M:di]+=c[di-1]*MU[di]*DD[1:(M-1)//di+1]
    residual=np.cumsum(jumps)[1:]-s*PSI[1:M]
    k=np.arange(M-1);values=[]
    for u in U:
        geo=np.exp(-(u/M)*k);terms=residual*geo
        b=float(terms.sum());den=float(np.abs(terms).sum())
        values.append(dict(u=float(u),margin_div_q=b,relative=b/den if den else 0))
    worst=min(values,key=lambda r:r['relative'])
    return dict(M=M,source=float(s),channel1=float(c[0]),worst=worst,
                negative_count=sum(r['relative']< -1e-9 for r in values),values=values)

if __name__=='__main__':
    start=time.monotonic();z=np.load('/root/rh-mobius-divisor-coordination-20260906/source.npz')
    D=z['defect'];D[0]=0;MU=z['mu'];ABEL=z['abel'];DD=np.diff(D,prepend=0)
    k=np.arange(len(D));PSI=z['psi']-k+2*0.577215664901532860606512090082;PSI[0]=0
    U=np.logspace(-3,4,113);ends=[2**e for e in range(10,21)]+[1865411]
    with pool.get_context('fork').Pool(8) as p:rows=list(p.imap(scan,ends))
    firstcoef=D[1]*(ABEL[1:-1]-z['direct'][1:-1]);bad=np.flatnonzero(firstcoef< -1e-8)+2
    old=json.loads((ROOT/'geometric_cross.json').read_text())
    nondeg=min((r for r in old['rows'] if r['M']>2),key=lambda r:r['scaled'])
    audits=[audit(nondeg['M'],str(round(nondeg['q'],8)),dps) for dps in (60,100)]
    out=dict(rows=rows,fast_coefficient_first_failure=int(bad[0]) if len(bad) else None,
             fast_coefficient_failure_count=len(bad),fast_coefficient_min=float(firstcoef.min()),
             small_nondegenerate=nondeg,small_audits=audits,seconds=time.monotonic()-start)
    (ROOT/'geometric_scale.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({**{k:v for k,v in out.items() if k!='rows'},'rows':[{k:v for k,v in r.items() if k!='values'} for r in rows]},indent=2))

"""Exhaustive endpoint search using finite arithmetic identities. Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1")
import json
import math
import multiprocessing as mp
from pathlib import Path
import time
import numpy as np

ROOT=Path(__file__).resolve().parent
SOURCE=Path('/root/rh-mobius-divisor-coordination-20260906')


def jumps(worker):
    out=np.zeros((3,N+1))
    # The two pieces partition ALL pairs d*q<=N.
    for d in range(worker+1,CUT+1,8):
        if not MU2[d]:
            continue
        q=N//d
        slots=slice(d,(q+1)*d,d)
        out[0,slots]+=d*DA[1:q+1]
        out[1,slots]+=2*math.sqrt(d)*DB[1:q+1]
        out[2,slots]+=DC[1:q+1]
    for q in range(worker+1,N//(CUT+1)+1,8):
        d=np.arange(CUT+1,N//q+1)
        mask=MU2[d]
        slots=slice((CUT+1)*q,(N//q+1)*q,q)
        out[0,slots]+=mask*d*DA[q]
        out[1,slots]+=2*mask*np.sqrt(d)*DB[q]
        out[2,slots]+=mask*DC[q]
    return out


def direct_diagonal(M):
    d=np.arange(1,M+1)
    q=M//d
    k=np.sqrt(d)*ABEL[q-1]+D[q]*(M-d*q)/(math.sqrt(M)+np.sqrt(d*q))
    return float(np.sum(MU2[1:M+1]*k*k)/(M*M))


if __name__=='__main__':
    started=time.monotonic()
    with np.load(SOURCE/'source.npz') as data:
        D,ABEL,DIRECT=(data[k] for k in ('defect','abel','direct'))
        MU2=data['mu'].astype(float)**2
    N=len(D)-1
    CUT=math.isqrt(N)
    q=np.arange(N+1)
    c=np.zeros(N+1)
    c[1:]=ABEL[:-1]-np.sqrt(q[1:])*D[1:]
    DA=np.diff(c*c,prepend=0)
    DB=np.diff(c*D,prepend=0)
    DC=np.diff(D*D,prepend=0)
    coefficients=np.zeros((3,N+1))
    with mp.get_context('fork').Pool(8) as pool:
        for part in pool.imap(jumps,range(8)):
            coefficients+=part
    np.cumsum(coefficients,axis=1,out=coefficients)
    M=np.arange(1,N+1)
    diagonal=(coefficients[0,1:]+coefficients[1,1:]*np.sqrt(M)+coefficients[2,1:]*M)/(M*M)
    source=DIRECT[:-1]/M
    ratio=np.divide(source*source,diagonal,out=np.zeros_like(source),where=diagonal>0)
    # Equality/empty cases are isolated from numerical rejection logic.
    apparent=np.flatnonzero((M>=3)&(ratio>1+1e-8))+1
    indices=np.argpartition(ratio[2:],-10)[-10:]+2
    indices=indices[np.argsort(ratio[indices])[::-1]]
    candidates=sorted(set(apparent.tolist()+[int(i+1) for i in indices]))
    audited=[]
    for m in candidates:
        value=direct_diagonal(m)
        audited.append(dict(M=m,source=float(source[m-1]),diagonal=value,
                            ratio=float(source[m-1]**2/value),
                            recurrence_error=float(diagonal[m-1]-value)))
    previous_error=0.0
    for phase in ('discovery','validation'):
        old=json.loads((SOURCE/('arithmetic-'+phase+'.json')).read_text())
        for band in old['bands']:
            for row in band['rows']:
                m=row['M']
                previous_error=max(previous_error,abs(diagonal[m-1]-row['ensembles'][0]))
    np.savez_compressed(ROOT/'all-endpoints.npz',M=M,source=source,diagonal=diagonal,ratio=ratio)
    result=dict(N=N,seconds=time.monotonic()-started,workers=8,
                apparent_violations=apparent.tolist(),max_previous_diagonal_error=previous_error,
                top_direct=sorted(audited,key=lambda r:r['ratio'],reverse=True),
                equality_M2=dict(source=float(source[1]),diagonal=float(diagonal[1]),ratio=float(ratio[1])))
    (ROOT/'search.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

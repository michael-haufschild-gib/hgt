"""Attack every nonnegative decreasing time kernel at fixed endpoints. Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json,time,traceback
import multiprocessing as mp
import numpy as np
from scipy.optimize import nnls
ROOT=Path(__file__).resolve().parent


def matrix(M):
    k=np.arange(1,M)
    v=np.empty((M,M-1))
    for d in range(1,M+1):
        v[d-1]=MU[d]*np.cumsum(D[k//d])
    return v


def solve(M):
    started=time.monotonic()
    v=matrix(M)
    scale=np.linalg.norm(v,axis=0)
    assert np.all(scale>0)
    vn=v/scale
    rows=[]
    for orientation in (1,-1):
        target=np.full(M,float(orientation))
        try:
            a,residual=nnls(vn,target,maxiter=20*M)
            actual=a/scale
            y=v@actual
            source=float(np.sum(y)); diagonal=float(y@y)
            gradient=vn.T@(y-target)
            rows.append(dict(sign=orientation,source=source,diagonal=diagonal,
                             ratio=source*source/diagonal if diagonal else 0,
                             projection_norm_sq=diagonal,residual=residual,
                             min_gradient=float(gradient.min()),
                             max_complementarity=float(np.max(np.abs(a*gradient))),
                             active=[dict(t=int(i+1),coefficient=float(value))
                                     for i,value in enumerate(actual) if value>0],
                             coefficients=actual.tolist()))
        except Exception:
            rows.append(dict(sign=orientation,error=traceback.format_exc()))
    return dict(M=M,seconds=time.monotonic()-started,orientations=rows)


if __name__=='__main__':
    start=time.monotonic()
    z=np.load('/root/rh-mobius-divisor-coordination-20260906/source.npz')
    D=z['defect'][:1025]; MU=z['mu'][:1025]
    D[0]=0
    with mp.get_context('fork').Pool(6) as pool:
        rows=pool.map(solve,[16,32,64,128,256,512])
    result=dict(seconds=time.monotonic()-start,endpoints=rows,workers=6)
    (ROOT/'search.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps([dict(M=row['M'],seconds=row['seconds'],
                          tests=[{k:test[k] for k in ('sign','ratio','projection_norm_sq','min_gradient','max_complementarity') if k in test} if 'error' not in test else test for test in row['orientations']]) for row in rows],indent=2))

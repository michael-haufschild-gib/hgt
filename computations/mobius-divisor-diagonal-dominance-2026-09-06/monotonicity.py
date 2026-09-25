"""Exhaustive SD2 test and independent update audit. Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1")
import numpy as np
import json
import math
import time
from pathlib import Path
import mpmath as mp
from audit import endpoint

ROOT=Path(__file__).resolve().parent
started=time.monotonic()
x=np.load(ROOT/'all-endpoints.npz'); m=x['M']
e=(x['diagonal']-x['source']**2)*m*m
step=np.diff(e); bad=np.flatnonzero(step < -1e-10)
indices=sorted(set(bad[:1].tolist()+[int(np.argmin(step))]))
z=np.load('/root/rh-mobius-divisor-coordination-20260906/source.npz')
D,A,mu=(z[k] for k in ('defect','abel','mu'))
rows=[]
for i in indices:
    M=int(m[i]); d=np.arange(1,M+1); q=M//d
    c=mu[d]*(np.sqrt(d)*A[q-1]+D[q]*(M-d*q)/(math.sqrt(M)+np.sqrt(d*q)))
    v=mu[d]*D[q]; w=1/(math.sqrt(M+1)+math.sqrt(M))
    S=float(np.sum(c)); V=float(np.sum(v))
    mixed=float(np.dot(c,v)); point=float(np.dot(v,v))
    diagonal_step=2*w*mixed+w*w*point
    source_square_step=2*w*S*V+w*w*V*V
    rows.append(dict(M=M,margin=float(e[i]),next_margin=float(e[i+1]),
                     recurrence_change=float(step[i]),
                     direct_update_change=diagonal_step-source_square_step,
                     diagonal_change=diagonal_step,source_square_change=source_square_step,
                     mixed=mixed,point_diagonal=point,source=S,source_increment_over_weight=V))
# Independent original-double-sum audit of the first rejection at both precisions.
checks=[]
first=int(m[indices[0]])
for precision in (60,100):
    s,q,_=endpoint(first,precision); margin=(q-s*s)*first*first
    s,q,_=endpoint(first+1,precision); next_margin=(q-s*s)*(first+1)**2
    checks.append(dict(dps=precision,change=mp.nstr(next_margin-margin,75)))
result=dict(claim='SD2: raw diagonal minus source square is nondecreasing at integer endpoints',
            N=int(m[-1]),failures=int(len(bad)),examples=rows,first_high_precision=checks,
            seconds=time.monotonic()-started)
(ROOT/'monotonicity.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

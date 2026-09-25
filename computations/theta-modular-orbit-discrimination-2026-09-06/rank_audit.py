"""Independent high-rank theta-shell audit, and exact seam polynomial candidate."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json,time,math,multiprocessing as pool
import mpmath as mp
import sympy as sy
from audit import step
from seam_ranks import pivots
ROOT=Path(__file__).resolve().parent
def audit(dps):
    mp.mp.dps=dps;pol=[[mp.mpf(0),mp.mpf(-6),mp.mpf(4)]]
    for _ in range(44):pol.append(step(pol[-1]))
    f=[mp.fsum(mp.exp(-mp.pi*n*n)*mp.polyval(list(reversed(p)),mp.pi*n*n) for n in range(1,21)) for p in pol]
    H=1+2*mp.fsum(mp.exp(-mp.pi*n*n) for n in range(1,21))
    c=[(-1)**k*mp.fsum((-1)**j*math.comb(2*k,j)*f[j]*f[2*k-j] for j in range(2*k+1))/H**2 for k in range(23)]
    return dict(dps=dps,shells=20,moments=[mp.nstr(v,70) for v in c],**pivots(c))
if __name__=='__main__':
    start=time.monotonic()
    with pool.Pool(2) as p:rows=list(p.imap(audit,(80,120)))
    (ROOT/'rank_audit.json').write_text(json.dumps(dict(rows=rows,seconds=time.monotonic()-start),indent=2)+'\n')
    print(json.dumps(dict(rows=rows,seconds=time.monotonic()-start),indent=2))

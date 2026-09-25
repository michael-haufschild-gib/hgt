"""Complete the preregistered S=-3 and S=0 event recording; Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json,time,multiprocessing as pool
import numpy as np
from scipy.integrate import solve_ivp
ROOT=Path(__file__).resolve().parent
def rhs(x,y):
    S,A,W=y
    return (3-S*S/3-3*A/4,-2*A*W,2+A/2+2*S*S/9-2*S*W/3)
def run(item):
    label,X,tol=item
    def low(t,y):return y[0]+3
    def high(t,y):return y[0]
    def cap(t,y):return 1e5-np.linalg.norm(y)
    low.direction=-1;high.direction=1;cap.direction=-1;cap.terminal=True
    sol=solve_ivp(rhs,(0,5),(0,X,0),events=(low,high,cap),rtol=tol,atol=tol/10,method='DOP853')
    return dict(label=label,X=X,rtol=tol,minus_three_crossings=sol.t_events[0].tolist(),
        zero_up_crossings=[float(t) for t in sol.t_events[1] if t>1e-8],
        norm_cap=sol.t_events[2].tolist(),end=float(sol.t[-1]),final_state=sol.y[:,-1].tolist(),success=sol.success)
if __name__=='__main__':
    start=time.monotonic();rows=json.loads((ROOT/'results.json').read_text())['rows']
    items=[(r['label'],r['X'],tol) for r in rows for tol in (2e-12,5e-14)]
    with pool.Pool(8) as p:out=list(p.imap(run,items))
    (ROOT/'events.json').write_text(json.dumps(dict(rows=out,seconds=time.monotonic()-start),indent=2)+'\n')
    print(json.dumps(dict(seconds=time.monotonic()-start,rows=out),indent=2))

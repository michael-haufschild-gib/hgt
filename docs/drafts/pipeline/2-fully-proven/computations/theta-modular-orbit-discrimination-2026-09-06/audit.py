"""Independent complete-density jet approximation, not an ODE differentiation. Runpod."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json,time,multiprocessing as pool,math
import mpmath as mp
ROOT=Path(__file__).resolve().parent

def step(p):
    out=[mp.mpf(0)]*(len(p)+1)
    for j,c in enumerate(p):out[j]+=(mp.mpf('.5')+2*j)*c;out[j+1]-=2*c
    return out

def audit(item):
    xstr,dps=item;mp.mp.dps=dps;x=mp.mpf(xstr)
    pol=[[mp.mpf(0),mp.mpf(-6),mp.mpf(4)]]
    for _ in range(8):pol.append(step(pol[-1]))
    f=[mp.fsum(mp.exp(x/2-mp.pi*n*n*mp.exp(2*x))*mp.polyval(list(reversed(p)),mp.pi*n*n*mp.exp(2*x)) for n in range(1,21)) for p in pol]
    H=mp.exp(x/2)*(1+2*mp.fsum(mp.exp(-mp.pi*n*n*mp.exp(2*x)) for n in range(1,21)))
    pp=[mp.fsum((-1)**k*math.comb(m,k)*f[k]*f[m-k] for k in range(m+1)) for m in (0,2,4,6,8)]
    p0,p2,p4,p6,p8=pp
    terms=[p0*p4*p8,-p0*p6*p6,-p2*p2*p8,2*p2*p4*p6,-p4**3]
    value=mp.fsum(terms)/H**6
    return dict(x=xstr,dps=dps,source_f0=mp.nstr(f[0],65),D1_mass_normalized=mp.nstr(value,65),relative=mp.nstr(mp.fsum(terms)/mp.fsum(abs(t) for t in terms),65),shells=20)

if __name__=='__main__':
    start=time.monotonic();items=[(x,p) for x in ('0','0.02','0.05','0.0685','0.1','0.2','0.3') for p in (70,110)]
    with pool.get_context('fork').Pool(8) as p:rows=list(p.imap(audit,items))
    out=dict(rows=rows,seconds=time.monotonic()-start,interpretation='Independent 20-shell numerical source audit; no rigorous tail enclosure, no Lean premise.')
    (ROOT/'audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

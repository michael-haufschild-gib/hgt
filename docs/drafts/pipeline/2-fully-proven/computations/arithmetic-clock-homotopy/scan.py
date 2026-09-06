"""Runpod-only exploration of the frozen exponential-clock family."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[key]='1'
import concurrent.futures
import json
import math
import mpmath as mp
from mpmath.functions.zeta import _hurwitz_em

def disable_fast(*args,**kwargs):
    raise NotImplementedError
mp.mp._zetasum_fast=disable_fast

def hurwitz_em(s,a):
    # Explicit EM branch; no negative-real-part reflection formula.
    first,second=_hurwitz_em(mp.mp,s,a,0,mp.mp.prec+20,False)
    return first+second

def endpoint_tail(u,a,x):
    m=int(mp.floor(x-a))
    c=a+m
    q=c+1
    tq=(-hurwitz_em(u,q+1)-q**(1-u)/(1-u)-q**(-u)/2)/(u*(u+1))
    def primitive(y):
        return (y**(1-u)/(1-u)+(2*c+1)*y**(-u)/u-c*(c+1)*y**(-u-1)/(u+1))/2
    return tq+primitive(q)-primitive(x)

def work(params):
    h_text,ratio_text,k=params
    exp_log=float(h_text)*k/float(ratio_text)
    mp.mp.dps=110+math.ceil(4*max(0,exp_log/math.log(10)-math.log10(float(h_text))))
    h,ratio=mp.mpf(h_text),mp.mpf(ratio_text)
    lam=2*mp.pi*ratio
    a=1/h
    t=lam/h
    u=mp.mpc(-1,-t)
    b=a*mp.exp(h*k/ratio)
    value=mp.im(a*a**(-mp.j*t)*(endpoint_tail(u,a,a)-endpoint_tail(u,a,b)))
    return dict(h=h_text,ratio=ratio_text,k=k,dps=mp.mp.dps,
                endpoint_log=mp.nstr(mp.log(b/a),30),value=mp.nstr(value,80),positive=bool(value>0))

if __name__=='__main__':
    grid=[(h,r,k) for h in ('0.01','0.1','0.25','0.5','1','2','4','8')
          for r in ('0.25','0.5','0.75','0.99') for k in (1,2,4)]
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        rows=list(pool.map(work,grid))
    with open('results.json','w') as out:
        json.dump(rows,out,indent=2)
    print(json.dumps([x for x in rows if x['positive']],indent=2),flush=True)

"""Hostile all-rank direction probe for the exact ODE family. Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json,time,multiprocessing as pool
import mpmath as mp
ROOT=Path(__file__).resolve().parent
RANK=12
def convolution(a,b,n):return mp.fsum(a[k]*b[n-k] for k in range(n+1))
def moments(X):
    N=4*(RANK-1);s=[mp.mpf(0)];a=[X];w=[mp.mpf(0)];h=[mp.mpf(1)]
    for n in range(N+2):
        ss=convolution(s,s,n);sw=convolution(s,w,n);aw=convolution(a,w,n)
        sn=((3 if n==0 else 0)-ss/3-3*a[n]/4)/(n+1)
        an=-2*aw/(n+1)
        wn=((2 if n==0 else 0)+a[n]/2+2*ss/9-2*sw/3)/(n+1)
        hn=-convolution(s,h,n)/(6*(n+1))
        s.append(sn);a.append(an);w.append(wn);h.append(hn)
    f=[((n+2)*(n+1)*h[n+2]-h[n]/4)/2 for n in range(N+1)]
    return [(-1)**k*mp.factorial(2*k)*mp.fsum((-1)**j*f[j]*f[2*k-j] for j in range(2*k+1)) for k in range(2*RANK-1)]
def pivots(c):
    scales=[mp.sqrt(abs(c[2*i])) for i in range(RANK)]
    if any(t==0 for t in scales):return dict(error='zero diagonal scale')
    M=mp.matrix([[c[i+j]/(scales[i]*scales[j]) for j in range(RANK)] for i in range(RANK)])
    L=mp.eye(RANK);D=[]
    for i in range(RANK):
        d=M[i,i]-mp.fsum(L[i,k]**2*D[k] for k in range(i));D.append(d)
        if d==0:return dict(error='zero pivot',pivots=[mp.nstr(d,65) for d in D])
        for j in range(i+1,RANK):L[j,i]=(M[j,i]-mp.fsum(L[j,k]*L[i,k]*D[k] for k in range(i)))/d
    return dict(pivots=[mp.nstr(d,65) for d in D],first_negative=next((i+1 for i,d in enumerate(D) if d<0),None))
def run(item):
    label,value,dps=item;mp.mp.dps=dps
    theta=1+2*mp.fsum(mp.exp(-mp.pi*n*n) for n in range(1,21));actual=(mp.pi*theta**4)**2
    X=actual*(1+mp.mpf(value)) if label.startswith('theta') else mp.mpf(value)
    c=moments(X)
    return dict(label=label,X=mp.nstr(X,70),dps=dps,moments=[mp.nstr(v,70) for v in c],**pivots(c))
if __name__=='__main__':
    start=time.monotonic()
    values=[str(x) for x in (6.25,10,15,17,18,19,19.1,19.15,19.157,19.16,19.2,20,21,25,30,40)]
    items=[('X='+x,x,80) for x in values]+[('theta','0',80),('theta','0',120)]
    items += [('theta_delta='+sgn+'1e-'+str(p),sgn+'1e-'+str(p),80) for p in (2,4,6,8,10,12) for sgn in ('','-')]
    with pool.Pool(8) as p:rows=list(p.imap(run,items))
    out=dict(rank=RANK,rows=rows,seconds=time.monotonic()-start)
    (ROOT/'seam_ranks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(seconds=out['seconds'],rows=[{k:v for k,v in r.items() if k not in ('X','moments')} for r in rows]),indent=2))

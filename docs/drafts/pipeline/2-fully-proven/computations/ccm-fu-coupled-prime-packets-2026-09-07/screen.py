"""Bounded RunPod diagnostic; numerical output never enters Lean."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
import csv, json, math, multiprocessing as mp, time
from pathlib import Path
import numpy as np
LIMIT=512
OUT=Path(__file__).resolve().parent
GAMMA=np.longdouble('0.577215664901532860606512090082402431')

def prepare():
    global MU,D,B
    tau=np.zeros(LIMIT+1,dtype=np.int64)
    for d in range(1,LIMIT+1):tau[d::d]+=1
    prime=np.ones(LIMIT+1,dtype=bool);prime[:2]=False
    for p in range(2,math.isqrt(LIMIT)+1):
        if prime[p]:prime[p*p::p]=False
    MU=np.ones(LIMIT+1,dtype=np.int8);MU[0]=0
    for p in np.flatnonzero(prime):
        MU[p::p]*=-1
        MU[p*p::p*p]=0
    n=np.arange(1,LIMIT+1,dtype=np.longdouble)
    D=np.zeros(LIMIT+1,dtype=np.longdouble)
    D[1:]=np.cumsum(np.log(n))-np.cumsum(tau[1:])+2*GAMMA*n
    B=np.zeros(LIMIT+2,dtype=np.longdouble)
    B[2:]=np.cumsum(D[1:]/(np.sqrt(n+1)+np.sqrt(n)))

def channel(M):
    d=np.arange(1,M,dtype=np.int64);q=M//d
    vals=MU[d]*(np.sqrt(d.astype(np.longdouble))*B[q]+(np.sqrt(np.longdouble(M))-np.sqrt((q*d).astype(np.longdouble)))*D[q])
    return np.sum(vals[d%2==1]),np.sum(vals[d%2==0])

def profile(M):
    h,b=channel(M)
    k=M//2
    w=(np.sqrt(np.longdouble(M)/2)-np.sqrt(np.longdouble(k)))/(np.sqrt(np.longdouble(k+1))-np.sqrt(np.longdouble(k)))
    predicted=-np.sqrt(np.longdouble(2))*((1-w)*channel(k)[0]+w*channel(k+1)[0])
    return dict(K=M,head=float(h),two=float(b),total=float(h+b),reflection_error=float(b-predicted))

def cross(a,b):return a['head']*b['two']-a['two']*b['head']

def main():
    t=time.monotonic();prepare()
    with mp.get_context('fork').Pool(min(8,os.cpu_count() or 1)) as pool:rows=pool.map(profile,range(2,LIMIT+1),chunksize=16)
    angles=sorted(math.atan2(r['two'],r['head']) for r in rows if math.hypot(r['head'],r['two'])>1e-12)
    gaps=[b-a for a,b in zip(angles,angles[1:])]+[angles[0]+2*math.pi-angles[-1]]
    # A containing half-plane excludes a strict positive circuit without a cubic search.
    candidates=rows if max(gaps)<math.pi-1e-10 else []
    witness=None
    for c in candidates:
        if witness:break
        earlier=[r for r in rows if r['K']<c['K']]
        for a in earlier:
            if witness:break
            for b in earlier:
                if a['K']>=b['K']:continue
                weights=[cross(b,c),cross(c,a),cross(a,b)]
                tol=1e-10
                if min(weights)>tol or max(weights)<-tol:
                    if max(weights)<0:weights=[-w for w in weights]
                    witness=dict(cutoffs=[a['K'],b['K'],c['K']],vectors=[[r['head'],r['two']] for r in [a,b,c]],positive_weights=weights)
                    break
    angles=sorted(math.atan2(r['two'],r['head']) for r in rows if math.hypot(r['head'],r['two'])>1e-12)
    gaps=[b-a for a,b in zip(angles,angles[1:])]+[angles[0]+2*math.pi-angles[-1]]
    summary=dict(limit=LIMIT,workers=min(8,os.cpu_count() or 1),cpu_count=os.cpu_count(),numpy=np.__version__,elapsed_seconds=time.monotonic()-t,strict_plane_witness=witness,max_direction_gap=max(gaps),head_min=min(rows,key=lambda r:r['head']),head_max=max(rows,key=lambda r:r['head']),two_min=min(rows,key=lambda r:r['two']),two_max=max(rows,key=lambda r:r['two']),max_reflection_error=max(abs(r['reflection_error']) for r in rows))
    with (OUT/'profiles.csv').open('w') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    (OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()

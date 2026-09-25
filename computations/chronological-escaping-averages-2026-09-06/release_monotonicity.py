"""Frozen J-test; Runpod only. Three independent coefficient cones, four BLAS threads."""
import os
os.environ['OPENBLAS_NUM_THREADS']='4'
os.environ['OMP_NUM_THREADS']='4'
import pathlib,sys,json,time,concurrent.futures
import numpy as np
from scipy.linalg.interpolative import svd
from scipy.optimize import linprog
ROOT=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'chronological-arithmetic-averaging-20260906'))
import kernel_reference as ex
N,M=8192,4096
KINDS=['sign_preserving','squarefree_box','full_box']


def solve(kind):
    start=time.time()
    A,e,_,_=ex.design(N,24)
    mu=ex.mobius(N)[1:].astype(float)
    indices=np.arange(M,N)
    if kind!='full_box': indices=indices[mu[indices]!=0]
    signs=mu[indices] if kind!='full_box' else np.ones(len(indices))
    B=np.asfortranarray(A[:,indices]*signs)
    b=e+A[:,:M]@mu[:M]
    U,s,V=svd(B,min(60,min(B.shape)-1),rand=False)
    p=U.T@b
    hi=min(45,int(np.sum(s>1e-15*s[0])))
    lower=0. if kind=='sign_preserving' else -1.
    opts={'time_limit':60.,'primal_feasibility_tolerance':1e-10,
          'dual_feasibility_tolerance':1e-10,'ipm_optimality_tolerance':1e-10}
    old=np.load(ROOT/('final_%d_%d.npz'%(N,M)))['a']
    choices=[('positive_average',old)]
    diagnostics=[]
    best_rank=1

    def assemble(x):
        a=np.zeros(N)
        a[:M]=mu[:M]
        a[indices]=signs*np.clip(x,lower,1.)
        return a

    for rank in range(1,hi+1):
        eq=V[:,:rank].T
        rhs=-p[:rank]/s[:rank]
        fit=linprog(np.zeros(len(indices)),A_eq=eq,b_eq=rhs,bounds=(lower,1.),
                    method='highs-ipm',options=opts)
        row={'phase':'exact','rank':rank,'status':int(fit.status),'message':fit.message}
        if not fit.success:
            diagnostics.append(row)
            break
        x=fit.x.copy()
        x+=V[:,:rank]@(rhs-eq@x)
        a=assemble(x)
        row['actual_norm']=float(np.linalg.norm(e+A@a))
        choices.append(('exact_%d'%rank,a))
        diagnostics.append(row)
        best_rank=rank
    for lo in sorted({max(1,best_rank-d) for d in [2,4,6]}):
        tail=(s[lo:hi]/s[lo])[:,None]*V[:,lo:hi].T
        target=p[lo:hi]/s[lo]
        fit=linprog(np.r_[np.zeros(len(indices)),1.],
                    A_ub=np.vstack([np.column_stack([tail,-np.ones(hi-lo)]),
                                    np.column_stack([-tail,-np.ones(hi-lo)])]),
                    b_ub=np.r_[-target,target],
                    A_eq=np.column_stack([V[:,:lo].T,np.zeros(lo)]),
                    b_eq=-p[:lo]/s[:lo],
                    bounds=[(lower,1.)]*len(indices)+[(0,None)],method='highs-ipm',options=opts)
        row={'phase':'balanced','lo':lo,'hi':hi,'status':int(fit.status),'message':fit.message}
        if fit.success:
            x=fit.x[:-1].copy()
            x+=V[:,:lo]@(-p[:lo]/s[:lo]-V[:,:lo].T@x)
            a=assemble(x)
            row['actual_norm']=float(np.linalg.norm(e+A@a))
            choices.append(('balanced_%d'%lo,a))
        diagnostics.append(row)
    label,a=min(choices,key=lambda z:np.linalg.norm(e+A@z[1]))
    np.savez_compressed(ROOT/('release_initial_%s.npz'%kind),a=a)
    row={'kind':kind,'selected':label,'norm':float(np.linalg.norm(e+A@a)),
         'variables':len(indices),'hi':hi,'best_exact_rank':best_rank,
         'diagnostics':diagnostics,'seconds':time.time()-start}
    print(json.dumps({k:v for k,v in row.items() if k!='diagnostics'}),flush=True)
    return row


def finalize(kind):
    import mpmath as mp
    mp.mp.dps=80
    A,e,_,_=ex.design(N,24)
    V,v,t,_=ex.design(N,60,True)
    mu=ex.mobius(N)[1:].astype(float)
    candidates=[(k,np.load(ROOT/('release_initial_%s.npz'%k))['a'])
                for k in KINDS[:KINDS.index(kind)+1]]
    label,a=min(candidates,key=lambda z:np.linalg.norm(e+A@z[1]))
    r=V@a+v
    ar=A@a+e
    idx=np.arange(M,N)
    if kind!='full_box':idx=idx[mu[idx]!=0]
    B=A[:,idx]*(mu[idx] if kind!='full_box' else 1.)
    b=e+A[:,:M]@mu[:M]
    grad=B.T@ar
    linear_min=np.minimum(grad,0.).sum() if kind=='sign_preserving' else -np.abs(grad).sum()
    dual=max(0.,float(b@ar+linear_min)/np.linalg.norm(ar))
    spots=np.unique(np.r_[np.geomspace(1e-9/N,20.,20),np.geomspace(.01/N,30./N,12)])
    diffs=[]
    for t0 in spots:
        tt=mp.mpf(float(t0))
        rr=mp.exp(-tt)+mp.fsum(mp.mpf(float(c))*(1/(j*tt)-1/mp.expm1(j*tt))
                              for j,c in enumerate(a,1) if c)
        rf=np.exp(-t0)+ex.bose_h(t0*np.arange(1,N+1))@a
        diffs.append(float(abs(rr-float(rf))))
    w=a[mu!=0]/mu[mu!=0]
    row={'kind':kind,'retained_from':label,'norm':float(np.linalg.norm(r)),
         'training_norm':float(np.linalg.norm(ar)),'quadrature_dual_norm':dual,
         'max_mp80_difference':max(diffs),'mp_spots':len(spots),
         'head_exact':bool(np.array_equal(a[:M],mu[:M])),
         'coefficient_bound':float(np.max(np.abs(a))),
         'sign_preserving':bool(np.all(a[mu!=0]*mu[mu!=0]>=0)),
         'nonsquarefree_zero':bool(np.all(a[mu==0]==0)),
         'positive_envelope_increments':int(np.sum(np.diff(w)>1e-8)),
         'left_tail_energy_bound':1e-30,'harmonic_tail_energy':float(r[-1]**2)}
    np.savez_compressed(ROOT/('release_%s.npz'%kind),a=a)
    np.savetxt(ROOT/('release_%s.csv'%kind),np.column_stack([np.arange(1,N+1),mu,a]),
               delimiter=',',header='k,mu,a',comments='',fmt=['%d','%d','%.17g'])
    print(json.dumps({'event':'validated',**row}),flush=True)
    return row


if __name__=='__main__':
    start=time.time()
    with concurrent.futures.ProcessPoolExecutor(max_workers=3) as p:
        search=list(p.map(solve,KINDS))
    with concurrent.futures.ProcessPoolExecutor(max_workers=3) as p:
        checked=list(p.map(finalize,KINDS))
    (ROOT/'release_results.json').write_text(json.dumps({'search':search,'results':checked,
        'seconds':time.time()-start,'status':'exploratory_not_certified'},indent=2))
    print(json.dumps({'event':'complete','seconds':time.time()-start}),flush=True)

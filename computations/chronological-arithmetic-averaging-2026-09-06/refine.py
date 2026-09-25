"""Positive simplex mode cancellation and nested-cutoff retention; Runpod only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='4'
os.environ['OMP_NUM_THREADS']='4'
import json,time,pathlib,concurrent.futures
import numpy as np
from scipy.linalg.interpolative import svd
from scipy.optimize import linprog
import kernel_reference as ex
import averaging as av
OUT=pathlib.Path(__file__).resolve().parent


def solve(n):
    start=time.time()
    A,e,_,_=ex.design(n,24)
    mu=ex.mobius(n)[1:].astype(float)
    R=e[:,None]+np.cumsum(A*mu[None,:],axis=1)
    U,s,V=svd(np.asfortranarray(R),min(60,min(R.shape)-1),rand=False)
    choices=[]
    for m in av.SIZES:
        if m<=n:
            alpha=np.pad(np.load(OUT/('case_%d.npz'%m))['alpha'],(0,n-m))
            choices.append(('nested_wolfe_%d'%m,alpha))
    diagnostics=[]
    for rank in range(8,46):
        eq=np.vstack([np.ones(n),V[:,:rank].T])
        rhs=np.r_[1.,np.zeros(rank)]
        fit=linprog(np.zeros(n),A_eq=eq,b_eq=rhs,bounds=(0,None),method='highs-ipm',
                    options={'time_limit':45.,'primal_feasibility_tolerance':1e-10,
                             'dual_feasibility_tolerance':1e-10})
        row={'rank':rank,'status':int(fit.status),'message':fit.message}
        if not fit.success:
            diagnostics.append(row)
            break
        alpha=np.maximum(fit.x,0.)
        support=alpha>1e-15
        X=eq[:,support]
        alpha[support]+=np.linalg.lstsq(X,rhs-X@alpha[support],rcond=1e-14)[0]
        alpha=np.maximum(alpha,0.)
        alpha/=alpha.sum()
        a=mu*np.clip(np.cumsum(alpha[::-1])[::-1],0.,1.)
        r=e+A@a
        row.update({'actual_norm':float(np.linalg.norm(r)),
                    'affine_error':float(np.max(np.abs(eq@alpha-rhs)))})
        choices.append(('exact_modes_%d'%rank,alpha))
        diagnostics.append(row)
    def score(choice):
        a=mu*np.clip(np.cumsum(choice[1][::-1])[::-1],0.,1.)
        return float(np.linalg.norm(e+A@a))
    label,alpha=min(choices,key=score)
    a=mu*np.clip(np.cumsum(alpha[::-1])[::-1],0.,1.)
    r=e+A@a
    dots=R.T@r
    norm=float(np.linalg.norm(r))
    positive=np.flatnonzero(alpha>0)
    probs=alpha[positive]
    order=np.argsort(positive)
    cumulative=np.cumsum(probs[order])
    quantiles=[int(positive[order[min(len(order)-1,np.searchsorted(cumulative,q))]]+1) for q in [.1,.5,.9]]
    row={'N':n,'selected':label,'norm':norm,'quadrature_dual_norm':max(0.,float(np.min(dots))/norm),
         'support_count':int(len(positive)),'min_cutoff':int(positive.min()+1),'max_cutoff':int(positive.max()+1),
         'cutoff_quantiles_10_50_90':quantiles,'terminal_weight':float(alpha[-1]),
         'mode_diagnostics':diagnostics,'seconds':time.time()-start}
    np.savez_compressed(OUT/('refined_%d.npz'%n),averaged=a,alpha=alpha)
    np.savetxt(OUT/('refined_coeff_%d.csv'%n),np.column_stack([np.arange(1,n+1),mu,a]),
               delimiter=',',header='k,mu,coefficient',comments='',fmt=['%d','%d','%.17g'])
    np.savetxt(OUT/('refined_support_%d.csv'%n),np.column_stack([positive+1,probs]),
               delimiter=',',header='cutoff,probability',comments='',fmt=['%d','%.17g'])
    print(json.dumps({k:v for k,v in row.items() if k!='mode_diagnostics'}),flush=True)
    return row


def check(n):
    import mpmath as mp
    mp.mp.dps=80
    a=np.load(OUT/('refined_%d.npz'%n))['averaged']
    V,v,t,_=ex.design(n,60,True)
    r=V@a+v
    spots=np.unique(np.r_[np.geomspace(1e-10/n,20.,36),np.geomspace(.01/n,30./n,16)])
    diffs=[]
    for x in spots:
        xx=mp.mpf(float(x))
        rr=mp.exp(-xx)+mp.fsum(mp.mpf(float(c))*(1/(j*xx)-1/mp.expm1(j*xx))
                              for j,c in enumerate(a,1) if c)
        rf=np.exp(-x)+ex.bose_h(x*np.arange(1,n+1))@a
        diffs.append(float(abs(rr-float(rf))))
    return {'N':n,'validation_norm':float(np.linalg.norm(r)),
            'max_mp80_residual_difference':max(diffs),'mp_spots':len(spots),
            'left_tail_energy_bound':1e-30,'harmonic_tail_energy':float(r[-1]**2),
            'coefficient_bound':float(np.max(np.abs(a))),
            'zero_nonsquarefree':bool(np.all(a[ex.mobius(n)[1:]==0]==0))}


if __name__=='__main__':
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as p:
        rows=list(p.map(solve,av.SIZES))
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as p:
        checks=list(p.map(check,av.SIZES))
    (OUT/'refined_results.json').write_text(json.dumps({'results':rows,'validation':checks},indent=2))
    print(json.dumps({'event':'complete','validation':checks}),flush=True)

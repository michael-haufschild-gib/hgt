"""Frozen positive cutoff windows. Run on authorized Runpod, never in Lean."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import json, time, pathlib, concurrent.futures, sys
import numpy as np
from scipy.linalg.interpolative import svd
from scipy.optimize import linprog

ROOT = pathlib.Path(__file__).resolve().parent
PRIOR = ROOT.parent/'chronological-arithmetic-averaging-20260906'
sys.path.insert(0, str(PRIOR))
import kernel_reference as ex
import averaging as av
SIZES = [512, 2048, 8192]
DIVISORS = [0, 64, 16, 4, 2]


def coefficients(mu, alpha, m):
    w = np.clip(np.cumsum(alpha[::-1])[::-1], 0., 1.)
    w[:m] = 1.
    return mu*w


def solve(case):
    n, divisor = case
    m = max(1, n//divisor) if divisor else 1
    started = time.time()
    A, e, _, _ = ex.design(n, 24)
    mu = ex.mobius(n)[1:].astype(float)
    R = e[:, None] + np.cumsum(A*mu, axis=1)
    X = np.asfortranarray(R[:, m-1:])
    alpha, wolfe = av.convex_minimum(X)
    choices = [('wolfe', np.r_[np.zeros(m-1), alpha])]
    old = np.load(PRIOR/('refined_%d.npz' % n))['alpha'].copy()
    old[:m-1] = 0.
    if old.sum() > 0:
        choices.append(('filtered_previous', old/old.sum()))
    U, s, V = svd(X, min(60, min(X.shape)-1), rand=False)
    ranks = []
    for rank in range(8, min(46, V.shape[1]+1)):
        eq = np.vstack([np.ones(X.shape[1]), V[:, :rank].T])
        rhs = np.r_[1., np.zeros(rank)]
        fit = linprog(np.zeros(X.shape[1]), A_eq=eq, b_eq=rhs,
                      bounds=(0, None), method='highs-ipm',
                      options={'time_limit':45., 'primal_feasibility_tolerance':1e-10,
                               'dual_feasibility_tolerance':1e-10})
        row = {'rank':rank, 'status':int(fit.status), 'message':fit.message}
        if not fit.success:
            ranks.append(row)
            break
        short = np.maximum(fit.x, 0.)
        mask = short > 1e-15
        Y = eq[:, mask]
        short[mask] += np.linalg.lstsq(Y, rhs-Y@short[mask], rcond=1e-14)[0]
        short = np.maximum(short, 0.)
        short /= short.sum()
        full = np.r_[np.zeros(m-1), short]
        a = coefficients(mu, full, m)
        row['actual_norm'] = float(np.linalg.norm(e+A@a))
        row['affine_error'] = float(np.max(np.abs(eq@short-rhs)))
        choices.append(('mode_%d' % rank, full))
        ranks.append(row)

    def score(item):
        return float(np.linalg.norm(e+A@coefficients(mu, item[1], m)))
    label, alpha = min(choices, key=score)
    a = coefficients(mu, alpha, m)
    np.savez_compressed(ROOT/('initial_%d_%d.npz' % (n,m)), a=a, alpha=alpha)
    row = {'N':n, 'M':m, 'divisor':divisor, 'selected':label,
           'norm':score((label,alpha)), 'support_count':int(np.sum(alpha>0)),
           'seconds':time.time()-started, 'wolfe':wolfe, 'ranks':ranks}
    print(json.dumps({k:v for k,v in row.items() if k not in ['wolfe','ranks']}), flush=True)
    return row


def finalize(n):
    import mpmath as mp
    mp.mp.dps = 80
    A,e,_,_ = ex.design(n,24)
    V,v,t,_ = ex.design(n,60,True)
    mu = ex.mobius(n)[1:].astype(float)
    windows = sorted({max(1,n//d) if d else 1 for d in DIVISORS})
    choices = [(m,np.load(ROOT/('initial_%d_%d.npz'%(n,m)))['alpha']) for m in windows]
    rows = []
    for m in windows:
        feasible = [(mm,al) for mm,al in choices if mm>=m]
        chosen,alpha = min(feasible, key=lambda z:np.linalg.norm(e+A@coefficients(mu,z[1],m)))
        a = coefficients(mu,alpha,m)
        r = V@a+v
        training = e+A@a
        norm = float(np.linalg.norm(r))
        raw = v+V@mu
        X = e[:,None]+np.cumsum(A*mu,axis=1)
        dual = max(0.,float(np.min(X[:,m-1:].T@training))/np.linalg.norm(training))
        spots = np.unique(np.r_[np.geomspace(1e-9/n,20.,20),np.geomspace(.01/n,30./n,12)])
        diffs = []
        for x in spots:
            xx = mp.mpf(float(x))
            rr = mp.exp(-xx)+mp.fsum(mp.mpf(float(c))*(1/(j*xx)-1/mp.expm1(j*xx))
                                    for j,c in enumerate(a,1) if c)
            rf = np.exp(-x)+ex.bose_h(x*np.arange(1,n+1))@a
            diffs.append(float(abs(rr-float(rf))))
        active = np.flatnonzero(alpha>0)
        u = np.geomspace(1e-7,80*n,1500)
        tt = u/n
        profile = (np.exp(-tt)+ex.bose_h(tt[:,None]*np.arange(1,n+1))@a)/np.sqrt(n)
        np.savez_compressed(ROOT/('final_%d_%d.npz'%(n,m)),a=a,alpha=alpha,u=u,profile=profile)
        np.savetxt(ROOT/('coeff_%d_%d.csv'%(n,m)),np.column_stack([np.arange(1,n+1),mu,a]),
                   delimiter=',',header='k,mu,a',comments='',fmt=['%d','%d','%.17g'])
        np.savetxt(ROOT/('support_%d_%d.csv'%(n,m)),np.column_stack([active+1,alpha[active]]),
                   delimiter=',',header='cutoff,probability',comments='',fmt=['%d','%.17g'])
        row = {'N':n,'M':m,'retained_from_M':chosen,'training_norm':float(np.linalg.norm(training)),
               'norm':norm,'quadrature_dual_norm':dual,'max_mp80_difference':max(diffs),
               'mp_spots':len(spots),'max_coefficient':float(np.max(np.abs(a))),
               'head_exact':bool(np.all(a[:m]==mu[:m])),
               'nonsquarefree_zero':bool(np.all(a[mu==0]==0)),
               'left_tail_energy_bound':1e-30,'harmonic_tail_energy':float(r[-1]**2),
               'support_count':int(len(active)), 'support_min':int(active.min()+1),
               'support_max':int(active.max()+1),
               'correction_norm':float(np.linalg.norm(r-raw))}
        rows.append(row)
        print(json.dumps({'event':'validated',**row}),flush=True)
    assert all(rows[i]['norm']<=rows[i+1]['norm']*(1+1e-6)+1e-15 for i in range(len(rows)-1))
    return rows


if __name__ == '__main__':
    start=time.time()
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        rows=list(pool.map(solve,[(n,d) for n in SIZES for d in DIVISORS]))
    (ROOT/'search.json').write_text(json.dumps(rows,indent=2))
    with concurrent.futures.ProcessPoolExecutor(max_workers=3) as pool:
        checked=list(pool.map(finalize,SIZES))
    (ROOT/'results.json').write_text(json.dumps({'status':'exploratory_not_certified',
        'results':checked,'workers':4,'blas_threads':4,'seconds':time.time()-start},indent=2))
    print(json.dumps({'event':'complete','seconds':time.time()-start}),flush=True)

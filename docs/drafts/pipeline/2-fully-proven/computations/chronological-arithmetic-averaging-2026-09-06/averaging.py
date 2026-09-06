"""Frozen arithmetic-averaging diagnostic. Runpod only; no Lean proof inputs.
Four independent cutoffs, four BLAS threads per worker. Feasible approximations
and floating-point quadrature dual diagnostics, never certified optima.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import json, math, time, pathlib, concurrent.futures
import numpy as np
from scipy.optimize import minimize_scalar
import kernel_reference as ex
OUT = pathlib.Path(__file__).resolve().parent
SIZES = [128, 512, 2048, 8192]


def convex_minimum(R, max_seconds=240):
    started = time.time()
    norms = np.einsum('ij,ij->j', R, R)
    support = [int(np.argmin(norms))]
    alpha = np.ones(1)
    best = (float(norms[support[0]]), support[:], alpha.copy())
    history = []
    status = 'iteration_limit'
    for it in range(2000):
        r = R[:, support] @ alpha
        energy = float(r@r)
        dots = R.T @ r
        j = int(np.argmin(dots))
        gap = energy-float(dots[j])
        if it % 10 == 0:
            history.append({'iteration': it, 'norm': math.sqrt(energy),
                            'support': len(support), 'fw_gap': gap})
        if energy < best[0]:
            best = (energy, support[:], alpha.copy())
        if gap <= max(1e-29, 1e-10*energy):
            status = 'floating_stationarity'
            break
        if time.time()-started > max_seconds:
            status = 'time_limit'
            break
        if j in support:
            status = 'active_vertex_stagnation'
            break
        support.append(j)
        alpha = np.r_[alpha, 0.]
        for inner in range(len(support)+10):
            X = R[:, support]
            if len(support) == 1:
                alpha = np.ones(1)
                break
            beta_tail = np.linalg.lstsq(X[:, 1:]-X[:, :1], -X[:, 0], rcond=1e-14)[0]
            beta = np.r_[1.-beta_tail.sum(), beta_tail]
            if np.min(beta) >= -1e-13:
                alpha = np.maximum(beta, 0.)
                alpha /= alpha.sum()
                break
            negative = beta < 0
            step = min(1., float(np.min(alpha[negative]/(alpha[negative]-beta[negative]))))
            alpha += step*(beta-alpha)
            keep = alpha > 1e-14
            if not np.any(keep):
                keep[np.argmax(alpha)] = True
            support = [v for v,k in zip(support,keep) if k]
            alpha = np.maximum(alpha[keep], 0.)
            alpha /= alpha.sum()
        else:
            status = 'inner_iteration_limit'
            break
    r = R[:, support]@alpha
    if float(r@r) < best[0]:
        best = (float(r@r), support[:], alpha.copy())
    energy, support, alpha = best
    full = np.zeros(R.shape[1])
    full[support] = alpha
    full /= full.sum()
    return full, {'status': status, 'iterations': it+1, 'seconds': time.time()-started,
                  'history': history, 'energy': energy}


def one_case(n):
    started = time.time()
    A, e, _, _ = ex.design(n, 24)
    mu = ex.mobius(n)[1:].astype(float)
    k = np.arange(1, n+1)
    lk = np.log(k)
    def objective(eps):
        r = e+A@(mu*np.exp(-eps*lk))
        return float(r@r)
    grid = np.unique(np.r_[0., np.geomspace(1e-8,.01,25), np.linspace(0,.5,101),
                           np.linspace(.5,4.,29)])
    values = np.array([objective(x) for x in grid])
    choices = [(float(v),float(x)) for x,v in zip(grid,values)]
    for i in np.argsort(values)[:8]:
        lo, hi = grid[max(0,i-1)], grid[min(len(grid)-1,i+1)]
        if lo < hi:
            fit = minimize_scalar(objective, bounds=(lo,hi),method='bounded',
                                  options={'xatol':1e-14})
            choices.append((float(fit.fun),float(fit.x)))
    energy, eps = min(choices)
    power = mu*np.exp(-eps*lk)
    R = e[:,None]+np.cumsum(A*mu[None,:],axis=1)
    alpha, diag = convex_minimum(R)
    weights = np.cumsum(alpha[::-1])[::-1]
    weights = np.clip(weights,0.,1.)
    averaged = mu*weights
    assert np.all(alpha >= 0) and abs(alpha.sum()-1) < 1e-14
    assert np.max(np.abs(averaged)) <= 1 and np.all(np.diff(weights)<=1e-14)
    r = e+A@averaged
    dots = R.T@r
    norm = float(np.linalg.norm(r))
    dual_norm = max(0.,float(np.min(dots))/norm) if norm else 0.
    result = {'N': n, 'epsilon':eps, 'epsilon_log_N':eps*math.log(n),
              'power_norm':math.sqrt(energy), 'raw_norm':float(np.linalg.norm(R[:,-1])),
              'best_raw_prefix_norm':float(np.min(np.linalg.norm(R,axis=0))),
              'convex_norm':norm, 'quadrature_dual_norm':dual_norm,
              'quadrature_relative_gap':(norm-dual_norm)/max(norm,1e-300),
              'terminal_weight':float(alpha[-1]), 'support_count':int(np.sum(alpha>0)),
              'solver':diag, 'seconds':time.time()-started}
    np.savez_compressed(OUT/('case_%d.npz'%n), power=power, averaged=averaged, alpha=alpha)
    np.savetxt(OUT/('coeff_%d.csv'%n), np.column_stack([k,mu,power,averaged,weights]),
               delimiter=',',header='k,mu,power_coefficient,average_coefficient,average_weight',
               comments='',fmt=['%d','%d','%.17g','%.17g','%.17g'])
    nz=np.flatnonzero(alpha)
    np.savetxt(OUT/('support_%d.csv'%n),np.column_stack([nz+1,alpha[nz]]),delimiter=',',
               header='cutoff,probability',comments='',fmt=['%d','%.17g'])
    print(json.dumps({'event':'case_done',**result}),flush=True)
    return result


def validate_case(row):
    import mpmath as mp
    mp.mp.dps=80
    n=row['N']
    data=np.load(OUT/('case_%d.npz'%n))
    V,v,t,_=ex.design(n,48,True)
    validations={}
    for label in ['power','averaged']:
        a=data[label]
        r=V@a+v
        spots=np.unique(np.r_[np.geomspace(1e-8/n,20.,32),np.geomspace(.01/n,20./n,12)])
        diffs=[]
        for x in spots:
            xx=mp.mpf(float(x))
            rr=mp.exp(-xx)+mp.fsum(mp.mpf(float(c))*(1/(j*xx)-1/mp.expm1(j*xx))
                                   for j,c in enumerate(a,1) if c)
            machine=math.exp(-x)+float(ex.bose_h(x*np.arange(1,n+1))@a)
            diffs.append(float(abs(rr-machine)))
        validations[label]={'l2_norm':float(np.linalg.norm(r)),
                            'mp80_max_residual_difference':max(diffs),
                            'left_tail_energy_bound':1e-30,
                            'harmonic_tail_energy':float(r[-1]**2),
                            'below_1_over_N_energy':float(r[t<1/n]@r[t<1/n]),
                            'correction_from_raw_norm':float(np.linalg.norm(V@(a-ex.mobius(n)[1:])))}
    return {'N':n,**validations}


if __name__=='__main__':
    start=time.time()
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        rows=list(pool.map(one_case,SIZES))
    (OUT/'results.json').write_text(json.dumps({'results':rows,'status':'exploratory_not_certified',
        'workers':4,'blas_threads_per_worker':4,'power_parameter_range':[0,4]},indent=2))
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        checks=list(pool.map(validate_case,rows))
    (OUT/'validation.json').write_text(json.dumps(checks,indent=2))
    print(json.dumps({'event':'complete','seconds':time.time()-start,'validation':checks}),flush=True)

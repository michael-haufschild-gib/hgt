"""Exploratory finite L2 approximation; results are never Lean proof inputs.
Run on the authorized Runpod. Four independent N cases, four BLAS threads each.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import json, math, time, pathlib, concurrent.futures
import numpy as np
from scipy.optimize import lsq_linear, minimize_scalar
from numpy.polynomial.legendre import leggauss

OUT = pathlib.Path(__file__).resolve().parent
C_MAX = 2.0
T_MAX = 80.0
SIZES = [16, 32, 64, 128, 256, 512]


def mobius(n):
    mu = np.ones(n + 1, dtype=np.int64)
    mu[0] = 0
    prime = np.ones(n + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, n + 1):
        if prime[p]:
            mu[p::p] *= -1
            prime[2*p::p] = False
            if p*p <= n:
                mu[p*p::p*p] = 0
    return mu


def bose_h(x):
    x = np.asarray(x)
    out = np.empty_like(x)
    small = x < .25
    y = x[small]
    z = y*y
    out[small] = .5 + y*(-1/12 + z*(1/720 + z*(-1/30240 + z*(1/1209600 + z*(-1/47900160 + z*(691/1307674368000))))))
    y = x[~small]
    out[~small] = 1/y - np.exp(-y)/(-np.expm1(-y))
    return out


def design(n, order, shifted=False):
    # Omitted lower-tail energy <= 1e-30 for every coefficient vector in [-2,2]^n.
    delta = 1e-30/(1+C_MAX*n)**2
    low, high = math.log(delta), math.log(T_MAX)
    step = .8 if shifted else 1.0
    edges = np.arange(low + (step/2 if shifted else 0), high, step)
    edges = np.unique(np.r_[low, edges, math.log(1/n), 0.0, high])
    nodes, weights = leggauss(order)
    x = ((edges[:-1, None]+edges[1:, None])/2 +
         (edges[1:, None]-edges[:-1, None])/2*nodes).ravel()
    w = ((edges[1:, None]-edges[:-1, None])/2*weights).ravel()*np.exp(x)
    t = np.exp(x)
    k = np.arange(1, n+1)
    A = np.sqrt(w)[:, None]*bose_h(t[:, None]*k)
    e = np.sqrt(w)*np.exp(-t)
    # For t>=80, h(kt)=1/(kt)+exponentially small remainder.
    A = np.vstack([A, 1/(math.sqrt(T_MAX)*k)])
    e = np.r_[e, 0.0]
    return A, e, np.r_[t, np.inf], delta


def damped_coeff(mu, eps):
    n = len(mu)-1
    b = np.zeros(n+1)
    for d in range(1, n+1):
        b[d::d] += (-eps)**(d-1)*mu[1:n//d+1]
    return b[1:]


def one_case(n):
    started = time.time()
    mu = mobius(n)
    k = np.arange(1, n+1)
    A, e, t, delta = design(n, 20)
    V, v, tv, _ = design(n, 36, shifted=True)
    models = {}

    def assess(label, coeff, extra=None):
        coeff = np.asarray(coeff)
        residual = A @ coeff + e
        validation = V @ coeff + v
        energy = float(residual @ residual)
        ve = float(validation @ validation)
        regions = [tv < 1/n, (tv >= 1/n) & (tv < 1), tv >= 1]
        mass = [float(validation[z] @ validation[z]) for z in regions]
        result = {'l2_norm': math.sqrt(ve), 'energy': ve,
                  'training_energy': energy, 'mesh_energy_difference': abs(ve-energy),
                  'left_tail_energy_bound': delta*(1+2*n)**2,
                  'max_abs_coefficient': float(np.max(np.abs(coeff))),
                  'energy_regions_t_lt_1_over_n__middle__t_ge_1': mass,
                  'first_quarter_mean_abs_deviation_from_mu': float(np.mean(np.abs(coeff[:max(1,n//4)]-mu[1:max(1,n//4)+1]))),
                  'harmonic_coefficient_sum': float(np.sum(coeff/k))}
        if extra: result.update(extra)
        models[label] = result
        np.savetxt(OUT/('coeff_%s_%d.csv' % (label,n)),
                   np.column_stack([k,mu[1:],coeff]), delimiter=',',
                   header='k,mu_k,a_k', comments='', fmt=['%d','%d','%.17g'])
        return result

    assess('raw', mu[1:].astype(float))
    assess('log_taper', mu[1:]*(1-np.log(k)/math.log(n+1)))
    def depth_objective(eps):
        r = A @ damped_coeff(mu, eps) + e
        return float(r @ r)
    depth = minimize_scalar(depth_objective, bounds=(0,.5), method='bounded',
                            options={'xatol':1e-10})
    eps = min([(0.0, depth_objective(0.0)),(.5,depth_objective(.5)),
               (float(depth.x),float(depth.fun))], key=lambda p:p[1])[0]
    assess('geometric_depth', damped_coeff(mu, eps), {'epsilon':eps})
    def abel_objective(tau):
        r = A @ (mu[1:]*np.exp(-tau*k/n)) + e
        return float(r @ r)
    abel = minimize_scalar(abel_objective, bounds=(0,30), method='bounded',
                           options={'xatol':1e-9})
    tau = min([(0.0,abel_objective(0.0)),(30.0,abel_objective(30.0)),
               (float(abel.x),float(abel.fun))], key=lambda p:p[1])[0]
    assess('arithmetic_abel',mu[1:]*np.exp(-tau*k/n), {'tau':tau})
    for C in [1.0,2.0]:
        solve_start = time.time()
        fit = lsq_linear(A, -e, bounds=(-C,C), method='trf', lsq_solver='exact',
                         tol=1e-13, max_iter=160)
        a = np.clip(fit.x,-C,C)
        r = A @ a + e
        gradient_half = A.T @ r
        # Fenchel lower bound for the QUADRATURE problem, not a continuum certificate.
        dual = 2*float(e @ r)-float(r @ r)-2*C*float(np.sum(np.abs(gradient_half)))
        assess('box%d' % C,a, {'coefficient_bound':C,'solver_status':int(fit.status),
                 'solver_iterations':int(fit.nit),'solver_optimality':float(fit.optimality),
                 'quadrature_dual_lower_bound':dual,
                 'quadrature_primal_dual_gap':float(r @ r)-dual,
                 'bound_active_count':int(np.sum(np.abs(a)>C-1e-6)),
                 'solve_seconds':time.time()-solve_start})
    # Archive a validation profile for the strongest box family.
    coeff = np.loadtxt(OUT/('coeff_box2_%d.csv'%n),delimiter=',',skiprows=1)[:,2]
    profile_t = np.geomspace(1e-6/n,20,1200)
    raw_profile = np.exp(-profile_t)+bose_h(profile_t[:,None]*k) @ mu[1:]
    box_profile = np.exp(-profile_t)+bose_h(profile_t[:,None]*k) @ coeff
    np.savez_compressed(OUT/('profile_%d.npz'%n),t=profile_t,raw=raw_profile,box2=box_profile)
    row = {'N':n,'quadrature_rows':len(e),'validation_rows':len(v),
           'target_energy_check':float(e @ e),'seconds':time.time()-started,'models':models}
    (OUT/('result_%d.json'%n)).write_text(json.dumps(row,indent=2))
    return row


def kernel_validation():
    import mpmath as mp
    mp.mp.dps = 80
    points = np.r_[np.geomspace(1e-35,.24,50),np.geomspace(.25,500,50)]
    errors = []
    for x,actual in zip(points,bose_h(points)):
        z = mp.mpf(float(x))
        reference = 1/z-1/mp.expm1(z)
        errors.append(float(abs(mp.mpf(float(actual))-reference)))
    return {'mpmath_digits':80,'sample_count':len(points),
            'maximum_absolute_kernel_error':max(errors)}


def make_plot(rows):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1,2,figsize=(11,4.3),layout='constrained')
    for key,label in [('raw','Raw Möbius'),('geometric_depth','Best geometric depth'),
                      ('log_taper','Log taper'),('arithmetic_abel','Best arithmetic Abel'),
                      ('box1','Box |a|≤1'),('box2','Box |a|≤2')]:
        axes[0].loglog([r['N'] for r in rows], [r['models'][key]['l2_norm'] for r in rows],
                      marker='o',markersize=4,label=label)
    axes[0].set(xlabel='N',ylabel='Validated finite L² error',title='Finite-scale comparison; numerical evidence')
    axes[0].legend(fontsize=8)
    data = np.load(OUT/('profile_%d.npz'%rows[-1]['N']))
    for key,label in [('raw','Raw Möbius'),('box2','Box |a|≤2')]:
        axes[1].loglog(data['t'],data['t']*data[key]**2,label=label)
    axes[1].axvline(1/rows[-1]['N'],color='gray',ls='--',lw=1)
    axes[1].set(xlabel='t',ylabel='Squared error per logarithmic time interval',
                title='Error location at N=%d'%rows[-1]['N'])
    axes[1].legend()
    fig.savefig(OUT/'comparison.png',dpi=170)


if __name__ == '__main__':
    started = time.time()
    print(json.dumps({'event':'start','sizes':SIZES,'workers':4,'blas_threads_per_worker':4}),flush=True)
    rows = []
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        pending = [pool.submit(one_case,n) for n in SIZES]
        for future in concurrent.futures.as_completed(pending):
            row = future.result()
            rows.append(row)
            print(json.dumps({'event':'case_done','N':row['N'],'seconds':row['seconds'],
                 'norms':{k:v['l2_norm'] for k,v in row['models'].items()}}),flush=True)
    rows.sort(key=lambda r:r['N'])
    result = {'status':'exploratory_not_proof','kernel_validation':kernel_validation(),
              'sizes':SIZES,'workers':4,'blas_threads_per_worker':4,
              'total_seconds':time.time()-started,'results':rows}
    (OUT/'results.json').write_text(json.dumps(result,indent=2))
    make_plot(rows)
    print(json.dumps({'event':'complete','seconds':time.time()-started}),flush=True)

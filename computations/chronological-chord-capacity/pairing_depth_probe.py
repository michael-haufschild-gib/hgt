"""Exploratory perfect-pairing enclosure depth. Run only on authorized Runpod.

Finite-grid LP suggests coefficients; nonlinear constraint exchange improves
monotone normalization. Neither sampled nor optimized values are certificates.
Each worker owns one seed; numerical-library threads are capped at one.
"""
import os
for name in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[name] = "1"

from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
import json
import time
import warnings
import numpy as np
import scipy
from scipy.optimize import linprog, minimize, OptimizeWarning


def matchings(points):
    if not points:
        return [()]
    return [((points[0], points[j]),) + a + b
            for j in range(1, len(points), 2)
            for a in matchings(points[1:j])
            for b in matchings(points[j+1:])]


def compositions(total, n):
    if n == 1:
        yield (total,)
    else:
        for a in range(total+1):
            for tail in compositions(total-a, n-1):
                yield (a,)+tail


def family_values(inc, probes):
    return np.prod(np.einsum("dri,ni->ndr", inc, probes), axis=2)


def value_gradient(inc, c, signs, k, z):
    g = signs*z
    windows = inc @ g
    products = np.prod(windows, axis=1)
    p = float(c @ products)
    grad = np.zeros(len(z))
    for j in range(inc.shape[1]):
        grad += np.einsum("d,di->i", c*np.prod(np.delete(windows,j,axis=1),axis=1), inc[:,j,:])
    S = float(g.sum())
    if k:
        grad = S**k*grad + k*S**(k-1)*p
    return S**k*p, grad*signs


def maximize(inc, c, signs, k, starts):
    n = len(signs)
    candidates = []
    for z in starts:
        z = np.maximum(z, 0)
        z = z/z.sum()
        v, _ = value_gradient(inc,c,signs,k,z)
        candidates.append((abs(v),z))
        for direction in (-1,1):
            def objective(w):
                a,b = value_gradient(inc,c,signs,k,w)
                return direction*a, direction*b
            res = minimize(objective,z,jac=True,method="SLSQP",bounds=[(0,1)]*n,
                           constraints={"type":"eq","fun":lambda w:w.sum()-1,
                                        "jac":lambda w:np.ones(n)},
                           options={"maxiter":200,"ftol":2e-12})
            if res.success and abs(res.x.sum()-1)<1e-7 and res.x.min()>-1e-8:
                w = np.maximum(res.x,0)
                w /= w.sum()
                candidates.append((abs(value_gradient(inc,c,signs,k,w)[0]),w))
    return max(candidates,key=lambda q:q[0])


def run_job(job):
    d,k,seed = job
    begin = time.monotonic()
    rng = np.random.default_rng(310000*d+17000*k+seed)
    n = 2*d-1
    diagrams = matchings(tuple(range(2*d)))
    inc = np.array([[[int(a<=i<b) for i in range(n)] for a,b in D] for D in diagrams],dtype=float)
    denominator = 10 if d==3 else 7
    grid = np.array(list(compositions(denominator,n)),dtype=float)/denominator
    grid = np.vstack((grid,rng.dirichlet(np.full(n,.35),size=800)))
    F = family_values(inc,grid)
    scale = np.max(np.abs(F),axis=0)
    if np.any(scale<=0):
        raise RuntimeError("degenerate sampled basis")
    lp_failures = 0

    def fit(g, current_F):
        nonlocal lp_failures
        A = current_F/scale
        objective = -(g.sum()**k)*family_values(inc,g[None,:])[0]/scale
        with warnings.catch_warnings():
            warnings.filterwarnings("ignore",message="(Unrecognized options detected|Unknown solver options).*",category=OptimizeWarning)
            res = linprog(objective,A_ub=np.vstack((A,-A)),b_ub=np.ones(2*len(A)),
                          bounds=[(None,None)]*len(scale),method="highs-ds",
                          options={"threads":1,"dual_feasibility_tolerance":1e-8,
                                   "primal_feasibility_tolerance":1e-8})
        if not res.success:
            lp_failures += 1
            return None
        return -float(res.fun),res.x/scale

    targets = []
    for i in range(40):
        a = rng.dirichlet(np.full(n,.35))
        signs = rng.choice((-1,1),size=n)
        if i<24:
            neg = int(rng.integers(n))
            a[neg] = 0
            a /= a.sum()
            loss = rng.uniform(.002,.32)
            a *= 1-loss
            a[neg] = loss
            signs = np.ones(n)
            signs[neg] = -1
        g = a*signs
        fitted = fit(g,F)
        if fitted:
            targets.append((fitted[0],g,fitted[1]))
    targets.sort(key=lambda q:q[0],reverse=True)
    trials = []
    for initial_score,g,c in targets[:3]:
        constraints = F.copy()
        exchange_iterations = 0
        for step in range(10):
            exchange_iterations += 1
            vals = np.abs(F@c)
            starts = grid[np.argsort(vals)[-12:]]
            M,w = maximize(inc,c,np.ones(n),0,starts)
            constraints = np.vstack((constraints,family_values(inc,w[None,:])))
            signs = np.where(g<0,-1.,1.)
            S,a = maximize(inc,c,signs,k,[np.abs(g)])
            g = signs*a
            fitted = fit(g,constraints)
            if fitted is None:
                break
            _,next_c = fitted
            relative_change = np.linalg.norm(next_c-c)/(1+np.linalg.norm(c))
            c = next_c
            if M<=1+2e-8 and relative_change<2e-8:
                break
        validation = np.vstack((grid,rng.dirichlet(np.full(n,.25),size=20000)))
        v = np.abs(family_values(inc,validation)@c)
        M,w = maximize(inc,c,np.ones(n),0,validation[np.argsort(v)[-40:]])
        signs = np.where(g<0,-1.,1.)
        S,a = maximize(inc,c,signs,k,[np.abs(g)])
        g = signs*a
        trials.append({"initial_grid_lp_score":initial_score,"sampled_monotone_max":float(v.max()),
                       "optimized_monotone_max":M,"optimized_sealed_value":S,"ratio_estimate":S/M,
                       "coefficients":c.tolist(),"signed_probe":g.tolist(),"monotone_probe":w.tolist(),
                       "exchange_iterations":exchange_iterations})
    best = max(trials,key=lambda q:q["ratio_estimate"])
    return {"degree":d,"depth":k,"seed":seed,"basis":diagrams,"grid_denominator":denominator,
            "initial_constraints":len(F),"lp_failures":lp_failures,"seconds":time.monotonic()-begin,
            "best":best,"trials":trials}


if __name__ == "__main__":
    jobs = [(d,k,s) for d,k in ((3,1),(4,1),(4,2)) for s in range(8)]
    results=[]
    out=Path("pairing-depth-results.json")
    metadata={"workers":24,"library_threads":1,"scipy":scipy.__version__,"numpy":np.__version__,
              "status":"running","purpose":"Numerical leads, never proof certificates"}
    with ProcessPoolExecutor(max_workers=24) as pool:
        pending={pool.submit(run_job,j):j for j in jobs}
        for future in as_completed(pending):
            try:
                result=future.result()
            except Exception as exc:
                result={"job":pending[future],"error":repr(exc)}
            results.append(result)
            out.write_text(json.dumps({"metadata":metadata,"results":results},indent=2)+"\n")
            if "best" in result:
                print(json.dumps({"degree":result["degree"],"depth":result["depth"],"seed":result["seed"],
                                  "ratio_estimate":result["best"]["ratio_estimate"]}),flush=True)
            else:
                print(json.dumps(result),flush=True)
    metadata["status"]="complete"
    out.write_text(json.dumps({"metadata":metadata,"results":results},indent=2)+"\n")

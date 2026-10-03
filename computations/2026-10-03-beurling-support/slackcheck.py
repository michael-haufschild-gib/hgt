# Fine-basis recheck of positive-slack claims: shifted pole data mu=1,2,3 and the dense log-grid support.
import os; os.environ['OPENBLAS_NUM_THREADS'] = '1'
import numpy as np, cvxpy as cp, json, sys
import multiprocessing as mpc
from threshold2 import setup

def kst(args):
    kind, par, L, hk, nonneg = args
    S = setup(L, [par if kind == "mu" else 0.0], hk); m = S["m"]
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S["A"] - np.log(np.pi)*S["G"] + S["P"])
    if kind == "mu":
        pts = list(range(2, int(np.floor(np.exp(L))) + 1))
    else:
        pts = list(np.exp(np.linspace(np.log(1.5), L, int(par))))
    Ms = [T(2/np.sqrt(x)*S["Sx"](np.log(x))) for x in pts]
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    prob = cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(m) >> 0] + ([lam >= 0] if nonneg else []))
    for solver, kw in ((cp.CLARABEL, dict(max_iter=3000)), (cp.SCS, dict(eps=1e-9, max_iters=100000))):
        try:
            prob.solve(solver=solver, **kw)
            if t.value is not None: return (kind, par, hk, nonneg, float(t.value))
        except Exception: continue
    return (kind, par, hk, nonneg, None)

if __name__ == "__main__":
    L = 2.5
    jobs = [("mu", mu, L, hk, False) for mu in (1.0, 2.0, 3.0) for hk in (0.05, 0.025)]
    jobs += [("grid", 120, L, hk, nn) for hk in (0.05, 0.025) for nn in (False, True)]
    with mpc.get_context("spawn").Pool(8) as pool:
        for r in pool.imap_unordered(kst, jobs):
            print(json.dumps(r), flush=True)

# S14: optimize K free atom positions x_k in (0, L) (weights free via SDP) to maximize kappa*(zeta datum).
# Does the optimum rediscover log(prime powers)?  Can K points beat kappa*=0?
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1'); os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('MKL_NUM_THREADS', '1')
import numpy as np, cvxpy as cp, json, sys
import multiprocessing as mpc
from scipy.optimize import minimize
from threshold2 import setup
from multiprocessing import Pool
NONNEG = os.environ.get('NONNEG', '1') == '1'
L = float(sys.argv[1]) if len(sys.argv) > 1 else 2.0; hk = float(sys.argv[3]) if len(sys.argv) > 3 else 0.05
S = setup(L, [0.0], hk); m = S["m"]
Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
Q0 = T(S["A"] - np.log(np.pi)*S["G"] + S["P"])
def kst(xs):
    if np.any(xs <= 0.05) or np.any(xs >= L - 0.02): return -5.0
    Ms = [T(2*np.exp(-x/2)*S["Sx"](x)) for x in xs]
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    prob = cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(m) >> 0] + ([lam >= 0] if NONNEG else []))
    for solver, kw in ((cp.CLARABEL, dict(max_iter=500)), (cp.SCS, dict(eps=1e-8, max_iters=20000))):
        try:
            prob.solve(solver=solver, **kw)
            if t.value is not None: return float(t.value)
        except Exception:
            continue
    return -5.0
def restart(args):
    K, seed = args
    rng = np.random.default_rng(seed)
    x0 = np.sort(rng.uniform(0.3, L - 0.1, K))
    res = minimize(lambda x: -kst(np.sort(x)), x0, method="Nelder-Mead", options=dict(maxfev=500, xatol=1e-5, fatol=1e-9))
    xs = np.sort(res.x)
    return dict(K=K, seed=seed, nonneg=NONNEG, kappa=-res.fun, atoms=[round(float(np.exp(x)), 4) for x in xs])
if __name__ == "__main__":
    pp = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32]
    ppL = [p for p in pp if np.log(p) < L]
    print(json.dumps(dict(L=L, prime_powers=ppL, kappa_primes=kst(np.log(np.array(ppL, float))))), flush=True)
    Ks = [int(k) for k in sys.argv[2].split(",")]
    jobs = [(K, s) for K in Ks for s in range(8)]
    with mpc.get_context('spawn').Pool(8) as pool:
        for r in pool.imap_unordered(restart, jobs):
            print(json.dumps(r), flush=True)

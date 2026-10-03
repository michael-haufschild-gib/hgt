import os; os.environ['OPENBLAS_NUM_THREADS'] = '1'
import numpy as np, cvxpy as cp, sys, json
from threshold2 import setup
L = float(sys.argv[1]); atoms = [float(a) for a in sys.argv[2].split(",")]
for hk in (0.05, 0.035, 0.025):
    S = setup(L, [0.0], hk); m = S["m"]
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S["A"] - np.log(np.pi)*S["G"] + S["P"])
    xs = np.log(atoms)
    Ms = [T(2*np.exp(-x/2)*S["Sx"](x)) for x in xs]
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    prob = cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(m) >> 0])
    for solver, kw in ((cp.CLARABEL, dict(max_iter=3000)), (cp.SCS, dict(eps=1e-10, max_iters=200000))):
        try:
            prob.solve(solver=solver, **kw)
            if t.value is not None: break
        except Exception: continue
    lv = lam.value
    Q = Q0 - sum(lv[i]*Ms[i] for i in range(len(Ms)))
    ev = np.linalg.eigvalsh(Q)
    print(json.dumps(dict(hk=hk, status=prob.status, t=float(t.value), exact_min_eig=float(ev[0]), lam=[round(float(x), 4) for x in lv])), flush=True)

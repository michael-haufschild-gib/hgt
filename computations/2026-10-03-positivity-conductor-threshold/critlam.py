# Critical producer lam_c of the even no-pole datum (Gamma_R, conductor q*), all n <= e^L, saved to npy.
import os; os.environ['OPENBLAS_NUM_THREADS'] = '8'
import numpy as np, cvxpy as cp, json, sys
from threshold2 import setup
L = float(sys.argv[1]); hk = float(sys.argv[2])
S = setup(L, [0.0], hk); m = S["m"]
Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
Q0 = T(S["A"] - np.log(np.pi)*S["G"])
Nmax = int(np.floor(np.exp(L)))
Ms = [T(2/np.sqrt(n)*S["Sx"](np.log(n))) for n in range(2, Nmax + 1)]
lam = cp.Variable(len(Ms)); t = cp.Variable()
prob = cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(m) >> 0])
for solver, kw in ((cp.CLARABEL, dict(max_iter=3000)), (cp.SCS, dict(eps=1e-9, max_iters=200000))):
    try:
        prob.solve(solver=solver, **kw)
        if t.value is not None: break
    except Exception: continue
lv = np.array(lam.value)
np.save("lamc_L%s_hk%s.npy" % (L, hk), lv)
print(json.dumps(dict(L=L, hk=hk, qstar=float(np.exp(-t.value)), lam=[round(float(x), 4) for x in lv[:30]])))

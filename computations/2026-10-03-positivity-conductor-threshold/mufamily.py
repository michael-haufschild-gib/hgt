# S10: shifted pole datum Gamma_R(s+mu) with pole term; prime-free threshold q*(mu) and critical producer lam_c(mu).
import numpy as np, cvxpy as cp, json, sys
from threshold2 import setup
from multiprocessing import Pool

def run(args):
    mu, L, hk = args
    S = setup(L, [mu], hk)   # Gamma_R(s+mu): psi(1/4 + mu/2 + ir/2)
    m = S["m"]
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S["A"] - np.log(np.pi)*S["G"] + S["P"])
    Nmax = int(np.floor(np.exp(L)))
    Ms = [T(2/np.sqrt(n)*S["Sx"](np.log(n))) for n in range(2, Nmax + 1)]
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    prob = cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(m) >> 0])
    try:
        prob.solve(solver=cp.CLARABEL, max_iter=2000)
        return dict(mu=mu, kstar=float(t.value), qstar=float(np.exp(-t.value)), lam=[round(float(x), 5) for x in lam.value[:10]])
    except Exception as e:
        return dict(mu=mu, err=str(e)[:60])

if __name__ == "__main__":
    L = float(sys.argv[1])
    mus = [-0.2, -0.1, -0.05, -0.02, -0.01, 0.0, 0.01, 0.02, 0.05, 0.1, 0.2]
    with Pool(6) as pool:
        for r in pool.map(run, [(mu, L, 0.05) for mu in mus]):
            print(json.dumps(r), flush=True)

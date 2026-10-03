# S11: pole-location family (pole at s=1+tau and s=-tau): P_tau = F(1/2+tau)F(-1/2-tau) sym;  and 2D (mu, w) grid.
import numpy as np, cvxpy as cp, json, sys
from threshold2 import setup
from multiprocessing import Pool

def kstar(mu, w, tau, L=2.5, hk=0.05):
    S = setup(L, [mu], hk); m = S["m"]
    hk2 = L/(m + 3); xs = -L/2 + 2*hk2 + hk2*np.arange(m)
    def Fvec(a):
        z = a*hk2/2; return hk2*np.exp(a*xs)*(np.sinh(z)/z)**4
    a = 0.5 + tau
    P = np.outer(Fvec(a), Fvec(-a)); P = P + P.T
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S["A"] - np.log(np.pi)*S["G"] + w*P)
    Nmax = int(np.floor(np.exp(L)))
    Ms = [T(2/np.sqrt(n)*S["Sx"](np.log(n))) for n in range(2, Nmax + 1)]
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    prob = cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(m) >> 0])
    try:
        prob.solve(solver=cp.CLARABEL, max_iter=2000); return float(t.value)
    except Exception:
        return None

def job(args):
    kind, a, b = args
    if kind == "tau": return (kind, a, b, kstar(0.0, 1.0, a))
    return (kind, a, b, kstar(a, b, 0.0))

if __name__ == "__main__":
    jobs = [("tau", t, 0) for t in (-0.1, -0.05, -0.02, -0.01, 0.0, 0.01, 0.02, 0.05, 0.1)]
    jobs += [("muw", mu, w) for mu in (-0.05, 0.0, 0.05) for w in (0.9, 0.95, 1.0, 1.05, 1.1)]
    with Pool(8) as pool:
        for r in pool.map(job, jobs):
            print(json.dumps(r), flush=True)

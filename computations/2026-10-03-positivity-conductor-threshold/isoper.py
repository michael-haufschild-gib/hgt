# S12: global sweep of the prime-free threshold Theta = -kappa* over degree-1 data (mu, w, tau) and degree-2 data.
import numpy as np, cvxpy as cp, json, sys
from threshold2 import setup
from multiprocessing import Pool

def kstar(mus, w, tau, L=2.5, hk=0.05):
    S = setup(L, list(mus), hk); m = S["m"]
    hk2 = L/(m + 3); xs = -L/2 + 2*hk2 + hk2*np.arange(m)
    def Fvec(a):
        z = a*hk2/2; return hk2*np.exp(a*xs)*(np.sinh(z)/z)**4
    a = 0.5 + tau
    P = np.outer(Fvec(a), Fvec(-a)); P = P + P.T
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S["A"] - len(mus)*np.log(np.pi)*S["G"] + w*P)
    Nmax = int(np.floor(np.exp(L)))
    Ms = [T(2/np.sqrt(n)*S["Sx"](np.log(n))) for n in range(2, Nmax + 1)]
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    prob = cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(m) >> 0])
    try:
        prob.solve(solver=cp.CLARABEL, max_iter=2000); return float(t.value)
    except Exception:
        return None

def job(p):
    mus, w, tau = p
    k = kstar(mus, w, tau)
    return dict(mus=mus, w=w, tau=tau, Theta_per_factor=None if k is None else -k/len(mus))

if __name__ == "__main__":
    rng = np.random.default_rng(7)
    pts = []
    for _ in range(40):
        pts.append(([float(rng.uniform(-0.5, 2.0))], float(rng.uniform(0, 3)), float(rng.uniform(-0.3, 0.3))))
    # targeted: large shifts with pole, big residues, poles near center, degree-2 shifted pairs with pole order 2
    for mu in (0.5, 1.0, 1.5, 2.0, 3.0): pts.append(([mu], 1.0, 0.0))
    for w in (1.5, 2.0, 3.0, 5.0): pts.append(([0.0], w, 0.0))
    for tau in (-0.25, -0.4, -0.45): pts.append(([0.0], 1.0, tau))
    for d in (0.1, 0.3, 1.0): pts.append(([d, -d], 2.0, 0.0))
    with Pool(8) as pool:
        res = pool.map(job, pts)
    res.sort(key=lambda r: (r["Theta_per_factor"] if r["Theta_per_factor"] is not None else 9))
    for r in res: print(json.dumps(r), flush=True)

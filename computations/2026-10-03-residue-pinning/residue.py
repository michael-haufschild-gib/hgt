# S7: is the pole residue pinned by positivity?  Feasible set {(w, lam): w*P + A - log(pi) G - sum lam_n M_n >= 0} at q=1.
# Preconditioned around (w, lam) = (1, Lambda): variables dw, dlam.  Report [min, max] of dw.  Also the arch-scale alpha.
import numpy as np, cvxpy as cp, json, sys, time
from weilform import *

def run(L, hk=0.05, floor=1e-15, extra="w"):
    S = setup(L, hk)
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    m = S["m"]; hk2 = S["hk"]; xs = S["xs"]
    def Fvec(a):
        z = a*hk2/2; return hk2*np.exp(a*xs)*(np.sinh(z)/z)**4
    P = np.outer(Fvec(0.5), Fvec(-0.5)); P = T(P + P.T)
    Nmax = int(np.floor(np.exp(L))); lamv = vonmangoldt(Nmax)
    Ms = [T(2/np.sqrt(n)*S["Sx"](np.log(n))) for n in range(2, Nmax + 1)]
    QL = T(S["Q0"]) - sum(lamv[n]*Ms[n - 2] for n in range(2, Nmax + 1))
    Q0full = T(S["Q0"])
    Arch = Q0full - P + np.log(np.pi)*np.eye(m)     # G-normalized arch part A
    mu, U = np.linalg.eigh(QL); Dm = 1/np.sqrt(np.maximum(mu, floor))
    pre = lambda M: (lambda X: (X + X.T)/2)((Dm[:, None]*(U.T @ M @ U))*Dm[None, :])
    # directions: +dw*P (pole residue), or +da*Arch (archimedean scale), minus dlam*M
    Dir = pre(P) if extra == "w" else pre(Arch)
    Ns = [pre(M) for M in Ms]
    sc = np.array([np.linalg.norm(X, 2) for X in Ns]); Ns = [X/s for X, s in zip(Ns, sc)]
    sd = np.linalg.norm(Dir, 2); Dir = Dir/sd
    y = cp.Variable(len(Ns)); z = cp.Variable()
    cons = [np.eye(m) + z*Dir - sum(y[i]*Ns[i] for i in range(len(Ns))) >> 0]
    res = []
    for sense in (cp.Minimize, cp.Maximize):
        prob = cp.Problem(sense(z), cons)
        try:
            prob.solve(solver=cp.CLARABEL, max_iter=1000)
            res.append(float(prob.value)/sd if prob.status in ("optimal", "optimal_inaccurate") else prob.status)
        except Exception:
            res.append("err")
    return dict(L=L, extra=extra, mu_min=float(mu[0]), interval=res)

if __name__ == "__main__":
    for extra in ("w", "alpha"):
        for L in (0.5, 0.8, 1.0, 1.2, 1.4, 1.6):
            print(json.dumps(run(L, extra=extra)), flush=True)

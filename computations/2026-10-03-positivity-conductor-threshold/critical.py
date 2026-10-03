# S8: the critical producer of the even no-pole datum at its threshold q*.  Does lam_crit converge in L?
# Null space of Q_{lam_crit} at q*: Fourier zeros of null vectors = "zeros" of the critical object.
import numpy as np, cvxpy as cp, json, sys
from threshold2 import setup
from weilform import Bhat

def crit(L, mus=(0.0,), pole=0, hk=0.05):
    import sys as _s
    hk = float(_s.argv[2]) if len(_s.argv) > 2 else hk
    pole = int(_s.argv[3]) if len(_s.argv) > 3 else pole
    S = setup(L, list(mus), hk); m = S["m"]
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S["A"] - len(mus)*np.log(np.pi)*S["G"] + pole*S["P"])
    Nmax = int(np.floor(np.exp(L)))
    Ms = [T(2/np.sqrt(n)*S["Sx"](np.log(n))) for n in range(2, Nmax + 1)]
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    prob = cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(m) >> 0])
    prob.solve(solver=cp.CLARABEL, max_iter=1000)
    lv = lam.value; tv = t.value
    Q = Q0 - sum(lv[i]*Ms[i] for i in range(len(Ms))) - tv*np.eye(m)
    ev, V = np.linalg.eigh(Q)
    # null vectors in original coefficients: c = Ci^T v
    hk2 = L/(m + 3); xs = -L/2 + 2*hk2 + hk2*np.arange(m)
    r = np.linspace(0.0, 60.0, 60001)
    F = hk2*np.cos(np.outer(r, xs))*Bhat(r*hk2)[:, None]   # even part of f-hat (null vectors of an even form are even/odd)
    Fo = hk2*np.sin(np.outer(r, xs))*Bhat(r*hk2)[:, None]
    zeros = []
    for k in range(3):
        c = Ci.T @ V[:, k]
        fe = F @ c; fo = Fo @ c
        f = fe if np.linalg.norm(fe) > np.linalg.norm(fo) else fo
        z = r[1:][np.sign(f[1:]) != np.sign(f[:-1])]
        zeros.append([round(float(x), 3) for x in z[:22]])
    return dict(L=L, qstar=round(float(np.exp(-tv)), 6), lam=[round(float(x), 4) for x in lv[:10]],
                eigs=[float("%.2e" % e) for e in ev[:5]], null_zeros=zeros)

if __name__ == "__main__":
    for L in [float(x) for x in sys.argv[1].split(",")]:
        print(json.dumps(crit(L)), flush=True)

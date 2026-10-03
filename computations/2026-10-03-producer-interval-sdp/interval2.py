# Preconditioned S4: lam = Lambda + delta; Q_Lambda = U diag(mu) U^T (G-normalized);
# feasibility  I - sum delta_n Dm U^T M_n U Dm >= 0  with Dm = diag(mu^{-1/2}) (eigenvalues floored at eps).
import numpy as np, cvxpy as cp, json, sys, time
from weilform import *

def interval(L, targets=(2, 3, 4, 5, 6), hk=0.05, floor=1e-15, mode="int"):
    hk = float(sys.argv[2]) if len(sys.argv) > 2 else hk
    S = setup(L, hk)
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Nmax = int(np.floor(np.exp(L)))
    lamv = vonmangoldt(Nmax)
    pts = [float(n) for n in range(2, Nmax + 1)] if mode == "int" else [n/2 for n in range(4, 2*Nmax + 1)]
    lamp = np.array([lamv[int(p)] if p == int(p) else 0.0 for p in pts])
    Ms = [T(2/np.sqrt(p)*S["Sx"](np.log(p))) for p in pts]
    QL = T(S["Q0"]) - sum(l*M for l, M in zip(lamp, Ms))
    mu, U = np.linalg.eigh(QL)
    mufl = np.maximum(mu, floor)
    Dm = 1/np.sqrt(mufl)
    Ns = [(Dm[:, None]*(U.T @ M @ U))*Dm[None, :] for M in Ms]
    Ns = [(X + X.T)/2 for X in Ns]
    sc = np.array([np.linalg.norm(X, 2) for X in Ns])
    Ns = [X/s for X, s in zip(Ns, sc)]
    y = cp.Variable(len(pts))
    d = cp.multiply(1/sc, y)
    cons = [np.eye(len(mu)) - sum(y[i]*Ns[i] for i in range(len(pts))) >> 0]
    out = dict(hk=hk, L=L, m=S["m"], nvar=len(pts), mode=mode, mu_min=float(mu[0]), mu_2=float(mu[1]),
               n_tiny=int(np.sum(mu < 1e-10)))
    for t in targets:
        if float(t) not in pts: continue
        i = pts.index(float(t)); res = []
        for sense in (cp.Minimize, cp.Maximize):
            prob = cp.Problem(sense(d[i]), cons)
            try:
                prob.solve(solver=cp.CLARABEL, max_iter=1000)
                res.append(float(prob.value) if prob.status in ("optimal", "optimal_inaccurate") else prob.status)
            except Exception as e:
                res.append("err")
        out[str(t)] = res
    return out

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "int"
    Ls = [float(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.3, 1.4, 1.5, 1.6, 1.7, 1.8, 2.0]
    for L in Ls:
        tg = tuple(range(2, int(np.floor(np.exp(L))) + 1)) if len(sys.argv) > 3 else (2, 3, 4, 5, 6)
        t0 = time.time(); r = interval(L, targets=tg, mode=mode); r["time"] = round(time.time() - t0, 1)
        print(json.dumps(r), flush=True)

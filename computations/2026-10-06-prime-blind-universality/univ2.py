# Basis refinement of the cross-optimality gaps between Gamma-shift data mu (even mu=0, odd mu=1, mu=4).
import numpy as np, cvxpy as cp, json, sys
from multiprocessing import Pool
from threshold2 import setup
TOL = dict(tol_gap_abs=1e-9, tol_gap_rel=1e-9, tol_feas=1e-9, max_iter=3000)
def solve(S, L, Q):
    m = S["m"]; Nmax = int(np.floor(np.exp(L)))
    X = cp.Variable((m, m), PSD=True)
    cons = [cp.trace(S["G"] @ X) == 1] + [cp.trace(S["Sx"](np.log(n)) @ X) == 0 for n in range(2, Nmax + 1)]
    p = cp.Problem(cp.Minimize(cp.trace(Q @ X)), cons); p.solve(solver=cp.CLARABEL, **TOL)
    return float(p.value), X.value, p.status
def run(hk):
    L = 2.5; mus = (0.0, 1.0, 4.0); Q, V, Xs, st = {}, {}, {}, {}
    for mu in mus:
        S = setup(L, [mu], hk); Q[mu] = S["A"] - np.log(np.pi)*S["G"]
        V[mu], Xs[mu], st[mu] = solve(S, L, Q[mu])
    gap = {"%g->%g" % (a, b): float("%.3e" % (np.sum(Q[b]*Xs[a]) - V[b])) for a in mus for b in mus if a != b}
    return dict(hk=hk, m=S["m"], V={str(k): round(v, 9) for k, v in V.items()}, status=st, gaps=gap)
if __name__ == "__main__":
    with Pool(4) as pool:
        for r in pool.imap_unordered(run, [0.05, 0.035, 0.025, 0.018]):
            print(json.dumps(r), flush=True)

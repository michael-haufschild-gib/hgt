# Basis-refinement check of the prime-blind thresholds (even/odd no-pole), via the dual (prime-blind cone) SDP:
# kappa* = min tr(Q0 X) s.t. X PSD, tr(G X)=1, tr(S_n X)=0   (= max over lam by duality); SCS + CLARABEL fallback.
import numpy as np, cvxpy as cp, json, sys, time
from threshold2 import setup

def kstar_dual(L, mus, pole, hk):
    S = setup(L, list(mus), hk); m = S["m"]
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S["A"] - len(mus)*np.log(np.pi)*S["G"] + pole*S["P"])
    Nmax = int(np.floor(np.exp(L)))
    Ms = [T(S["Sx"](np.log(n))) for n in range(2, Nmax + 1)]
    X = cp.Variable((m, m), PSD=True)
    cons = [cp.trace(X) == 1] + [cp.trace(M @ X) == 0 for M in Ms]
    prob = cp.Problem(cp.Minimize(cp.trace(Q0 @ X)), cons)
    for solver, kw in ((cp.CLARABEL, dict(max_iter=2000)), (cp.SCS, dict(eps=1e-9, max_iters=200000))):
        try:
            prob.solve(solver=solver, **kw)
            if prob.status in ("optimal", "optimal_inaccurate"):
                return float(prob.value), solver, prob.status
        except Exception:
            continue
    return None, None, "fail"

if __name__ == "__main__":
    for L in (2.0, 2.5):
        for hk in (0.05, 0.035, 0.025, 0.018):
            t0 = time.time(); rec = dict(L=L, hk=hk)
            for name, mus, pole in (("even", [0.0], 0), ("odd", [1.0], 0), ("zeta", [0.0], 1)):
                v, s, st = kstar_dual(L, mus, pole, hk)
                rec[name] = (round(float(np.exp(-v)), 5) if v is not None else None, None if v is None else float("%.3e" % v), str(s), st)
            rec["time"] = round(time.time() - t0, 1)
            print(json.dumps(rec), flush=True)

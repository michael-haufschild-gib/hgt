# S4: projection of the finite-support producer set W_L onto single weights.
# W_L = { lam on support set X (log of integers 2..e^L) : Q0 - 2 sum lam_n n^{-1/2} S(log n) >= 0 on the B-spline span }.
# Report [min, max] of lam_2, lam_3, lam_4, lam_6 for growing L; variants: lam >= 0; enlarged support (half-integers).
import numpy as np, cvxpy as cp, json, sys, time
from weilform import *

def interval(L, mode="int", nonneg=False, targets=(2, 3, 4, 6), hk=0.05):
    S = setup(L, hk)
    Gi = np.linalg.inv(np.linalg.cholesky(S["G"]))     # Gi G Gi^T = I
    T = lambda M: Gi @ M @ Gi.T
    Nmax = int(np.floor(np.exp(L)))
    if mode == "int":
        pts = [float(n) for n in range(2, Nmax + 1)]
    elif mode == "half":   # integers and half-integers
        pts = [n/2 for n in range(4, 2*Nmax + 1)]
    Q0 = T(S["Q0"]); Q0 = (Q0 + Q0.T)/2
    Ss = []
    for p in pts:
        M = T(2/np.sqrt(p)*S["Sx"](np.log(p))); Ss.append((M + M.T)/2)
    lam = cp.Variable(len(pts))
    Q = Q0 - sum(lam[i]*Ss[i] for i in range(len(pts)))
    cons = [Q >> 0]
    if nonneg: cons.append(lam >= 0)
    out = {}
    lamv = vonmangoldt(Nmax)
    for t in targets:
        if float(t) not in pts: continue
        i = pts.index(float(t)); res = []
        for sense in (cp.Minimize, cp.Maximize):
            prob = cp.Problem(sense(lam[i]), cons)
            try:
                prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-10, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=400)
                res.append(float(prob.value) if prob.status in ("optimal", "optimal_inaccurate") else prob.status)
            except Exception as e:
                res.append("err:" + str(e)[:40])
        out[t] = dict(interval=res, Lambda=round(float(lamv[t]), 6))
    return dict(L=L, m=S["m"], nvar=len(pts), mode=mode, nonneg=nonneg, res=out)

if __name__ == "__main__":
    mode = sys.argv[1]; nonneg = sys.argv[2] == "1"
    for L in [float(x) for x in sys.argv[3].split(",")]:
        t0 = time.time()
        r = interval(L, mode, nonneg); r["time"] = round(time.time() - t0, 1)
        print(json.dumps(r), flush=True)

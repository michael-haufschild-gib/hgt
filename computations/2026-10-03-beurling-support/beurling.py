# S13: ζ-datum positivity with weights supported on log of a Beurling system N_P (or modified sets).
import numpy as np, cvxpy as cp, json, sys
from threshold2 import setup
from multiprocessing import Pool

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

def beurling_set(gens, X):
    pts = {1.0}
    for p in gens:
        new = set()
        for x in pts:
            y = x*p
            while y <= X + 1e-9:
                new.add(y); y *= p
        pts |= new
    return sorted(x for x in pts if x > 1.0 + 1e-12)

def kstar(points, L=2.5, hk=0.05):
    S = setup(L, [0.0], hk); m = S["m"]
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S["A"] - np.log(np.pi)*S["G"] + S["P"])
    Ms = [T(2/np.sqrt(x)*S["Sx"](np.log(x))) for x in points]
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    prob = cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(m) >> 0])
    try:
        prob.solve(solver=cp.CLARABEL, max_iter=2000); return float(t.value)
    except Exception:
        return None

def job(spec):
    name, pts = spec
    return name, len(pts), kstar(pts)

if __name__ == "__main__":
    L = 2.5; X = np.exp(L)
    specs = [("N", beurling_set(PRIMES, X))]
    for d in (-0.1, -0.03, -0.01, -0.003, 0.003, 0.01, 0.03, 0.1):
        specs.append(("2->%+.3f" % d, beurling_set([2 + d] + PRIMES[1:], X)))
    for d in (-0.03, 0.03):
        specs.append(("3->%+.3f" % d, beurling_set([2, 3 + d] + PRIMES[2:], X)))
    specs.append(("N+halves", sorted(set(beurling_set(PRIMES, X)) | {k/2 for k in range(5, int(2*X) + 1, 2)})))
    specs.append(("N+{2.5}", sorted(set(beurling_set(PRIMES, X)) | {2.5})))
    specs.append(("N+{e}", sorted(set(beurling_set(PRIMES, X)) | {float(np.e)})))
    specs.append(("N-{4}", [x for x in beurling_set(PRIMES, X) if abs(x - 4) > 1e-9]))
    specs.append(("N-{6}", [x for x in beurling_set(PRIMES, X) if abs(x - 6) > 1e-9]))
    specs.append(("N-{7}", [x for x in beurling_set(PRIMES, X) if abs(x - 7) > 1e-9]))
    specs.append(("all reals grid", list(np.exp(np.linspace(np.log(1.5), L, 120)))))
    with Pool(8) as pool:
        for name, n, k in pool.map(job, specs):
            print("%-14s npts=%3d  kappa*=%s" % (name, n, ("%+.3e" % k) if k is not None else "fail"), flush=True)

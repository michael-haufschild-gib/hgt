# Solve pinning intervals from saved preconditioned matrices with box bounds (|y| <= B); report box hits as unbounded.
import numpy as np, cvxpy as cp, json, sys
from multiprocessing import Pool
f = sys.argv[1]; L = float(sys.argv[2])
Z = np.load(f); Ns = [Z["arr_%d" % i] for i in range(len(Z.files))]
sc = np.array([np.linalg.norm(X, 2) for X in Ns]); Ns = [X/s for X, s in zip(Ns, sc)]
m = Ns[0].shape[0]; B = 1e6
def solve(args):
    i, sense = args
    y = cp.Variable(len(Ns))
    cons = [np.eye(m) - sum(y[j]*Ns[j] for j in range(len(Ns))) >> 0, cp.abs(y) <= B]
    prob = cp.Problem((cp.Minimize if sense < 0 else cp.Maximize)(y[i]), cons)
    try:
        prob.solve(solver=cp.CLARABEL, max_iter=3000)
        v = float(prob.value)
        if abs(v) > 0.99*B: return (i, sense, "unbounded")
        return (i, sense, v/sc[i])
    except Exception as e:
        return (i, sense, "err")
with Pool(8) as pool:
    res = pool.map(solve, [(i, s) for i in range(len(Ns)) for s in (-1, 1)])
out = {}
for i, s, v in res: out.setdefault(i + 2, [None, None])[0 if s < 0 else 1] = v
print(json.dumps(dict(L=L, iv=out)))

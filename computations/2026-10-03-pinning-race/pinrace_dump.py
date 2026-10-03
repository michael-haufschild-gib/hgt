# Dump whitened LMI blocks A_n = W^T M_n W (W^T Q_Lambda W = I) for one spline family (env P) to JSON.
import mpmath as mp, json, sys, os
from hpweil import build, vm, P
DPS = int(os.environ.get("DPS", "70")); mp.mp.dps = DPS
L, hk, out = float(sys.argv[1]), float(sys.argv[2]), sys.argv[3]
B = build(L, hk, DPS); m = B["m"]; N = int(mp.floor(mp.e**mp.mpf(L))); lam = vm(N)
Ci = mp.inverse(mp.cholesky(B["G"]))
T = lambda M: (lambda X: (X + X.T)/2)(Ci*M*Ci.T)
Q0 = T(B["P"] - mp.log(mp.pi)*B["G"] + B["A"])
Ms = {n: T(B["S"](mp.log(n))*(2/mp.sqrt(n))) for n in range(2, N + 1)}
QL = Q0
for n in range(2, N + 1):
    if lam[n] != 0: QL = QL - lam[n]*Ms[n]
E, U = mp.eigsy(QL)
if min(E[i] for i in range(m)) <= 0: print("NOT PD"); sys.exit(1)
W = mp.matrix(m, m)
for c in range(m):
    for r in range(m): W[r, c] = U[r, c]/mp.sqrt(E[c])
blocks = {}
for n in range(2, N + 1):
    X = W.T*Ms[n]*W; X = (X + X.T)/2
    blocks[n] = [[mp.nstr(X[i, j], DPS) for j in range(m)] for i in range(m)]
json.dump(dict(L=L, hk=hk, P=P, m=m, N=N, low=mp.nstr(min(E[i] for i in range(m)), 4), blocks=blocks), open(out, "w"))
print("dumped", out, m, N)

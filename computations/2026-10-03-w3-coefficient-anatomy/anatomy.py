# S16: anatomy of the coefficients of visible W_3 elements (FE-null space of Gamma_R^3, entire, conductor 1).
import os; os.environ['OPENBLAS_NUM_THREADS'] = '8'
import numpy as np, json, sys
from scipy.linalg import svd
from afe import *
d = int(sys.argv[1]) if len(sys.argv) > 1 else 3
T = float(sys.argv[2]) if len(sys.argv) > 2 else 160.0
Tc = T + 60; nt = (Tc/(2*np.pi))**(d/2); N = int(np.ceil(4.0*nt)) + 5
n = np.arange(1, N + 1, dtype=float)
td = np.arange(0.05, Tc, 0.08)
D = defect_rows(td, n, d, 0.0, sigma0=3.0, c1=0.5, c2=2.5)
A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
U, s, Vt = svd(A, full_matrices=True); s = s/s[0]; s = np.concatenate([s, np.zeros(N - len(s))])
B = Vt[s < 1e-8].T
tg = np.arange(0.2, T, 0.05)
R = Zrows(tg, n, d, 0.0, a=0.02) @ B
u, sv, vt = np.linalg.svd(R, full_matrices=False)
top = 8
E = B @ vt[:top].T          # N x top: coefficient vectors of the most visible W directions (unit l2)
# arithmetic functions
def factor(m):
    f = {}; x = m; p = 2
    while p*p <= x:
        while x % p == 0: f[p] = f.get(p, 0) + 1; x //= p
        p += 1
    if x > 1: f[x] = f.get(x, 0) + 1
    return f
Om = np.array([sum(factor(int(m)).values()) if m > 1 else 0 for m in n])
om = np.array([len(factor(int(m))) if m > 1 else 0 for m in n])
sqf = np.array([all(v == 1 for v in factor(int(m)).values()) for m in n])
dd = np.ones(N)
for _ in range(d - 1):
    nd = np.zeros(N)
    for i in range(1, N + 1): nd[i-1::i] += dd[i-1]
    dd = nd
mu = np.array([0 if not s_ else (-1)**o for s_, o in zip(sqf, om)]); mu[0] = 1
out = dict(d=d, T=T, N=N, k=B.shape[1], sv=[float("%.3g" % x) for x in sv[:top]/np.sqrt(len(tg))])
rows = []
for j in range(top):
    e = E[:, j]
    w = e**2
    # where is the l2 mass?  by n-range, by Omega(n), squarefree, residue mod 2,3,4,6
    rng = {f"n<={c}": float(w[:c].sum()) for c in (10, 30, 100, 300)}
    byOm = {int(o): float(w[Om == o].sum()) for o in range(0, int(Om.max()) + 1)}
    base_Om = {int(o): float(np.mean(Om[n >= 2] == o)) for o in range(0, int(Om.max()) + 1)}
    # approximate multiplicativity on coprime pairs with m,n<=40 and mn<=N: corr(e_{mn}, e_m e_n / e_1?) -> use normalized e/e_1 is ill-posed (e_1 ~ 0)
    pairs = [(a, b) for a in range(2, 60) for b in range(a + 1, 60) if np.gcd(a, b) == 1 and a*b <= N]
    x = np.array([e[a*b - 1] for a, b in pairs]); y = np.array([e[a-1]*e[b-1] for a, b in pairs])
    mult_corr = float(np.corrcoef(x, y)[0, 1]) if len(pairs) > 3 else None
    corr_d = float(np.corrcoef(e, dd)[0, 1]); corr_mu = float(np.corrcoef(e, mu)[0, 1])
    res = {m: [float(w[(n.astype(int) % m) == r].sum()) for r in range(m)] for m in (2, 3, 4)}
    sign_sq = float(np.mean(np.sign(e[sqf]) > 0))
    rows.append(dict(j=j, mass_range=rng, mass_by_Omega={k: round(v, 3) for k, v in byOm.items()},
                     base_Omega={k: round(v, 3) for k, v in base_Om.items()}, mult_corr=mult_corr,
                     corr_d3=round(corr_d, 3), corr_mu=round(corr_mu, 3), residues={m: [round(v, 3) for v in r] for m, r in res.items()},
                     first=[round(float(v), 4) for v in e[:12]]))
out["rows"] = rows
np.save("W%d_T%d_top.npy" % (d, int(T)), E)
print(json.dumps(out))

# Near-null vectors of Q_{lam_c} (even no-pole datum at q*) in finer bases, lam_c fixed from the converged SDP (hk=0.05).
import numpy as np, json, sys
from threshold2 import setup
from weilform import Bhat
from critical import crit
L = 3.0
base = crit(L)                                      # hk=0.05 SDP solution (lam, q*)
# recover full lam vector by rerunning without truncation
import cvxpy as cp
S0 = setup(L, [0.0], 0.05)
Nmax = int(np.floor(np.exp(L)))
def lam_full():
    Ci = np.linalg.inv(np.linalg.cholesky(S0["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S0["A"] - np.log(np.pi)*S0["G"])
    Ms = [T(2/np.sqrt(n)*S0["Sx"](np.log(n))) for n in range(2, Nmax + 1)]
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(S0["m"]) >> 0]).solve(solver=cp.CLARABEL, max_iter=1000)
    return lam.value, t.value
lv, tv = lam_full()
zeta = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178, 40.918719, 43.327073, 48.005151, 49.773832]
out = dict(qstar=float(np.exp(-tv)), lam=[round(float(x), 4) for x in lv])
for hk in (0.05, 0.035, 0.025):
    S = setup(L, [0.0], hk); m = S["m"]
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q = T(S["A"] - np.log(np.pi)*S["G"]) - sum(lv[n - 2]*T(2/np.sqrt(n)*S["Sx"](np.log(n))) for n in range(2, Nmax + 1)) - tv*np.eye(m)
    ev, V = np.linalg.eigh(Q)
    hk2 = L/(m + 3); xs = -L/2 + 2*hk2 + hk2*np.arange(m)
    r = np.linspace(0.0, 52.0, 52001)
    Fe = hk2*np.cos(np.outer(r, xs))*Bhat(r*hk2)[:, None]
    common = None; allz = []
    for k in range(4):
        c = Ci.T @ V[:, k]; f = Fe @ c
        if np.linalg.norm(f) < 1e-8*np.linalg.norm(c): continue
        z = r[1:][np.sign(f[1:]) != np.sign(f[:-1])]
        allz.append(z)
    # zeros common to all near-null vectors (within 0.02)
    if allz:
        base_z = allz[0]
        comm = [x for x in base_z if all(np.min(np.abs(zz - x)) < 0.02 for zz in allz[1:])]
    else:
        comm = []
    near = [(round(float(x), 3), round(float(min(zeta, key=lambda g: abs(g - x))), 3)) for x in comm]
    out["hk=%g" % hk] = dict(m=m, eigs=[float("%.2e" % e) for e in ev[:4]], common_zeros=near)
print(json.dumps(out))

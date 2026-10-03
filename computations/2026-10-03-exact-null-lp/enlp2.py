# Exact-null pinning LP, full tail: minimize sum_{m != n0, 2<=m<=Mmax} w_m |I(m)|  s.t.  I(n0) = sgn,  nu >= 0.
# ghat = Xi^2 * sum nu_j Gaussian(t; c_j, SIG).  Unconditional: every lam in W has
#   sgn * delta(n0) n0^{-1/2} * 1 >= - sum_{m != n0} |delta(m)| m^{-1/2} |I(m)|,
# so with |delta(m)| <= b_m and w_m = b_m m^{-1/2}:  -/+ delta(n0) <= sqrt(n0) * OPT(sgn).
import mpmath as mp, numpy as np, json, sys, os
from scipy.optimize import linprog
from multiprocessing import Pool
mp.mp.dps = 30
TMAX, DT, SIG = float(os.environ.get("TMAX", "160")), float(os.environ.get("DT", "0.5")), float(os.environ.get("SIG", "1.0"))
MMAX, BEXP = int(os.environ.get("MMAX", "3000")), float(os.environ.get("BEXP", "1.0"))
tq = np.arange(0.0, TMAX + 6*SIG, 0.01)

def logxi2(t):
    s = mp.mpf(1)/2 + 1j*mp.mpf(t)
    v = s*(s - 1)/2*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
    a = abs(mp.re(v)); return float(2*mp.log(a)) if a > 0 else -1e300
def chunk(ts): return [logxi2(t) for t in ts]

if __name__ == "__main__":
    n0 = int(sys.argv[1])
    with Pool(8) as p: lx = np.concatenate(p.map(chunk, np.array_split(tq, 64)))
    centers = np.arange(DT, TMAX, DT); ms = np.arange(2, MMAX + 1); lg = np.log(ms)
    A = np.zeros((len(ms), len(centers)))
    for j, c in enumerate(centers):
        w = np.exp(-0.5*((tq - c)/SIG)**2); sel = w > 1e-20
        l = lx[sel]; dens = np.exp(l - l.max())*w[sel]
        A[:, j] = (np.cos(np.outer(lg, tq[sel]))*dens).sum(axis=1)*0.01
    i0 = int(np.where(ms == n0)[0][0]); others = [i for i in range(len(ms)) if i != i0]
    wts = ms[others]**(BEXP - 0.5)
    nv, no = len(centers), len(others)
    res = {}
    for sgn in tuple(int(x) for x in os.environ.get('SGNS', '1,-1').split(',')):
        c = np.concatenate([np.zeros(nv), wts])
        Aub = np.vstack([np.hstack([A[others], -np.eye(no)]), np.hstack([-A[others], -np.eye(no)])]); bub = np.zeros(2*no)
        Aeq = np.hstack([A[[i0]], np.zeros((1, no))]); beq = np.array([float(sgn)])
        r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=[(0, None)]*(nv + no), method="highs")
        if r.status != 0: res[sgn] = dict(status=str(r.message)[:80]); continue
        nu = r.x[:nv]; I = A @ nu
        res[sgn] = dict(OPT=float(r.fun), bound=float(np.sqrt(n0)*r.fun), mass=float(nu.sum()),
                        last=float(np.abs(I[-50:]).max()), nnz=int((nu > 1e-12*max(nu.max(), 1e-300)).sum()))
    print(json.dumps(dict(n0=n0, TMAX=TMAX, DT=DT, SIG=SIG, MMAX=MMAX, BEXP=BEXP, res=res)), flush=True)

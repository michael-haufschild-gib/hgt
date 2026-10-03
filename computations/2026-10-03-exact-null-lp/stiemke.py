# Stiemke test: does a fully supported prime-blind exact-null test exist (in truncation)?
# ghat = Xi^2 * sum nu_j Gaussian_j, constraints I(m) = int ghat cos(t log m) = 0 for 2<=m<=MMAX, sum nu = 1,
# nu_j >= tau  (tau maximized). tau*>0: interior point (no separator). tau*=0: the forced-zero bumps locate
# where a separator ("pseudo-producer", Xi^2 V_delta >= 0) carries its off-zero spectral mass.
import mpmath as mp, numpy as np, json, sys, os
from scipy.optimize import linprog
from multiprocessing import Pool
mp.mp.dps = 30
TMAX, DT, SIG, MMAX = float(os.environ.get("TMAX", "100")), float(os.environ.get("DT", "0.25")), float(os.environ.get("SIG", "1.0")), int(os.environ.get("MMAX", "100"))
tq = np.arange(0.0, TMAX + 6*SIG, 0.01)
def logxi2(t):
    s = mp.mpf(1)/2 + 1j*mp.mpf(t)
    v = s*(s - 1)/2*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
    a = abs(mp.re(v)); return float(2*mp.log(a)) if a > 0 else -1e300
def chunk(ts): return [logxi2(t) for t in ts]
if __name__ == "__main__":
    with Pool(8) as p: lx = np.concatenate(p.map(chunk, np.array_split(tq, 64)))
    centers = np.arange(DT, TMAX, DT); ms = np.arange(2, MMAX + 1); lg = np.log(ms)
    A = np.zeros((len(ms), len(centers)))
    for j, c in enumerate(centers):
        w = np.exp(-0.5*((tq - c)/SIG)**2); sel = w > 1e-20
        l = lx[sel]; dens = np.exp(l - l.max())*w[sel]
        A[:, j] = (np.cos(np.outer(lg, tq[sel]))*dens).sum(axis=1)*0.01
    nv = len(centers)
    # variables: nu (nv), tau ; maximize tau  <=> minimize -tau
    cvec = np.zeros(nv + 1); cvec[-1] = -1.0
    Aeq = np.vstack([np.hstack([A, np.zeros((len(ms), 1))]), np.hstack([np.ones((1, nv)), np.zeros((1, 1))])])
    beq = np.concatenate([np.zeros(len(ms)), [1.0]])
    Aub = np.hstack([-np.eye(nv), np.ones((nv, 1))]); bub = np.zeros(nv)      # tau - nu_j <= 0
    r = linprog(cvec, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=[(0, None)]*(nv + 1), method="highs")
    out = dict(TMAX=TMAX, DT=DT, SIG=SIG, MMAX=MMAX, status=r.status, msg=str(r.message)[:60])
    if r.status == 0:
        nu = r.x[:nv]; tau = r.x[-1]
        out.update(tau=float(tau), tau_rel=float(tau*nv), resid=float(np.abs(A @ nu).max()))
        # second LP: which bumps can be strictly positive at all?  maximize nu_j individually is costly; use
        # the support of a max-sum-of-min(nu,eps) proxy: maximize sum_j min(nu_j, 1/nv) via LP
        z = np.zeros(nv); 
        c2 = np.concatenate([np.zeros(nv), -np.ones(nv)])                    # vars nu, u ; u_j <= nu_j, u_j <= 1/nv
        Aub2 = np.vstack([np.hstack([-np.eye(nv), np.eye(nv)])]); bub2 = np.zeros(nv)
        Aeq2 = np.vstack([np.hstack([A, np.zeros((len(ms), nv))]), np.hstack([np.ones((1, nv)), np.zeros((1, nv))])])
        r2 = linprog(c2, A_ub=Aub2, b_ub=bub2, A_eq=Aeq2, b_eq=beq, bounds=[(0, None)]*nv + [(0, 1.0/nv)]*nv, method="highs")
        if r2.status == 0:
            u = r2.x[nv:]; dead = centers[u < 1e-9/nv]
            out.update(frac_alive=float((u > 1e-9/nv).mean()), dead_ranges=[[float(dead.min()), float(dead.max())]] if len(dead) else [],
                       dead_sample=[float(x) for x in dead[:40]])
    print(json.dumps(out), flush=True)

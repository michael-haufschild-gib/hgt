# Majorant-side exact-null LP, scaling in TMAX.
# Tests ghat = Xi(t)^2 * sum_j nu_j Gaussian(t; c_j, SIG), nu >= 0.  Q_Lambda(g) = 0 unconditionally.
# Every full-cone producer lam, with delta = Lambda - lam and |delta(m)| <= sqrt(m)(log m + C0), satisfies
#   delta(n0) >= -sqrt(n0) * sum_{m != n0} (1 + log m) |I(m)|   when I(n0) = +1,
# where I(m) = int Xi^2 hhat cos(t log m) dt.  OPT(T) -> 0 for every n0 would give lam <= Lambda, hence RH by Landau.
import mpmath as mp, numpy as np, json, sys, os, multiprocessing as mpr
from scipy.optimize import linprog

mp.mp.dps = 20

def logxi2(t):
    t = mp.mpf(t)
    z = mp.siegelz(t)
    if z == 0:
        return -1e300
    v = mp.log((t*t + mp.mpf(1)/4)/2) - mp.log(mp.pi)/4 + mp.re(mp.loggamma(mp.mpf(1)/4 + 1j*t/2)) + mp.log(abs(z))
    return float(2*v)

def chunk(ts):
    return [logxi2(t) for t in ts]

def run(n0, TMAX, DT, SIG, MMAX, pool):
    tq = np.arange(0.0, TMAX + 6*SIG, 0.01)
    lx = np.concatenate(pool.map(chunk, np.array_split(tq, 48)))
    centers = np.arange(DT, TMAX, DT)
    ms = np.arange(2, MMAX + 1); lg = np.log(ms)
    A = np.zeros((len(ms), len(centers)))
    for j, c in enumerate(centers):
        w = np.exp(-0.5*((tq - c)/SIG)**2); sel = w > 1e-20
        l = lx[sel]; dens = np.exp(l - l.max())*w[sel]
        A[:, j] = (np.cos(np.outer(lg, tq[sel]))*dens).sum(axis=1)*0.01
    i0 = int(np.where(ms == n0)[0][0]); others = [i for i in range(len(ms)) if i != i0]
    wts = 1.0 + lg[others]
    nv, no = len(centers), len(others)
    out = {}
    for sgn in (1, -1):
        c = np.concatenate([np.zeros(nv), wts])
        Aub = np.vstack([np.hstack([A[others], -np.eye(no)]), np.hstack([-A[others], -np.eye(no)])])
        bub = np.zeros(2*no)
        Aeq = np.hstack([A[[i0]], np.zeros((1, no))]); beq = np.array([float(sgn)])
        r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=[(0, None)]*(nv + no), method="highs")
        if r.status != 0:
            out[sgn] = dict(status=str(r.message)[:80]); continue
        nu = r.x[:nv]; I = A @ nu
        top = np.argsort(-np.abs(I[others]))[:8]
        out[sgn] = dict(OPT=float(r.fun), bound=float(np.sqrt(n0)*r.fun),
                        tail=float(np.abs(I[-100:]).max()),
                        support=[float(x) for x in centers[nu > 1e-6*nu.max()][[0, -1]]],
                        worst_m=[int(ms[others][k]) for k in top],
                        worst_I=[float(I[others][k]) for k in top])
        if sgn == 1:
            np.save(f"/root/qannplus/nu_n{n0}_T{int(TMAX)}_S{SIG}.npy", np.vstack([centers, nu]))
    return dict(n0=n0, TMAX=TMAX, DT=DT, SIG=SIG, MMAX=MMAX, res=out)

if __name__ == "__main__":
    os.environ["OMP_NUM_THREADS"] = "2"
    ctx = mpr.get_context("spawn")
    with ctx.Pool(3) as pool:
        for spec in sys.argv[1:]:
            n0, T, DT, SIG = spec.split(",")
            print(json.dumps(run(int(n0), float(T), float(DT), float(SIG), 3000, pool)), flush=True)

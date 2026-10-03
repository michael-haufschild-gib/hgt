# Exact-null selective LP: g = K_Phi * h, ghat = Xi(t)^2 * hhat(t), hhat = sum_j nu_j phi_j (Gaussian bumps, nu >= 0).
# Q_Lambda(g) = 0 unconditionally.  For lam in W:  sum_m delta(m) m^{-1/2} I(m) >= 0,  I(m) = int ghat cos(t log m) dt.
# Selectivity: I(m) = 0 (2<=m<=M, m != n0), I(n0) = 1.  Minimize tail  sum_{M<m<=M'} w_m |I(m)|,  w_m = log m
# (a-priori |delta(m)| <= sqrt(m) log m).  Then |delta(n0)| <= sqrt(n0) * T(M) * max_m |delta(m)|/(sqrt m log m).
import mpmath as mp, numpy as np, json, sys, os
from scipy.optimize import linprog
from multiprocessing import Pool
mp.mp.dps = 30
TMAX, DT, SIG = float(os.environ.get("TMAX", "160")), float(os.environ.get("DT", "0.5")), float(os.environ.get("SIG", "1.0"))
tq = np.arange(0.0, TMAX + 6*SIG, 0.02)                     # quadrature grid

def logxi2(t):
    s = mp.mpf(1)/2 + 1j*mp.mpf(t)
    v = s*(s - 1)/2*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
    a = abs(mp.re(v))
    return float(2*mp.log(a)) if a > 0 else -1e300

def chunk(ts): return [logxi2(t) for t in ts]

if __name__ == "__main__":
    n0 = int(sys.argv[1]); Ms = [int(x) for x in sys.argv[2].split(",")]; R = float(os.environ.get("RTAIL", "3"))
    with Pool(8) as p: lx = np.concatenate(p.map(chunk, np.array_split(tq, 64)))
    centers = np.arange(DT, TMAX, DT)
    Mmax = int(R*max(Ms)); ms = np.arange(2, Mmax + 1); lg = np.log(ms)
    A = np.zeros((len(ms), len(centers)))
    for j, c in enumerate(centers):
        w = np.exp(-0.5*((tq - c)/SIG)**2)
        sel = w > 1e-18
        l = lx[sel]; norm = l.max()
        dens = np.exp(l - norm)*w[sel]                       # Xi^2 * bump, normalized per bump
        A[:, j] = (np.cos(np.outer(lg, tq[sel]))*dens).sum(axis=1)*0.02
    out = []
    for M in Ms:
        Mp = int(R*M); eq = [i for i, m in enumerate(ms) if m <= M]; tail = [i for i, m in enumerate(ms) if M < m <= Mp]
        nv, nt = len(centers), len(tail)
        # variables: nu (nv) >= 0, s (nt) >= 0 with -s <= I_tail <= s
        c = np.concatenate([np.zeros(nv), np.log(ms[tail])])
        Aeq = np.hstack([A[eq], np.zeros((len(eq), nt))]); beq = np.array([1.0 if ms[i] == n0 else 0.0 for i in eq])
        Aub = np.vstack([np.hstack([A[tail], -np.eye(nt)]), np.hstack([-A[tail], -np.eye(nt)])]); bub = np.zeros(2*nt)
        r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=[(0, None)]*(nv + nt), method="highs")
        if r.status != 0:
            out.append(dict(M=M, status=r.message)); continue
        nu = r.x[:nv]; I = A @ nu
        beyond = [float(abs(I[i])*np.log(ms[i])) for i in range(len(ms)) if ms[i] > Mp]
        out.append(dict(M=M, Mp=Mp, T=float(r.fun), mass=float(nu.sum()), maxI_eq=float(np.abs(I[eq] - beq).max()),
                        tail_beyond_max=max(beyond) if beyond else 0.0, nnz=int((nu > 1e-12*nu.max()).sum())))
        print(json.dumps(out[-1]), flush=True)
    print(json.dumps(dict(n0=n0, TMAX=TMAX, DT=DT, SIG=SIG, res=out)))

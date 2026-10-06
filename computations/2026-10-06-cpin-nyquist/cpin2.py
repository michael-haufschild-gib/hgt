# C-PIN finite-level test with smoothness control.
# nu(t) = Z(t)^2 * h(t), h = sum_j nu_j phi_j, Gaussian bumps of width sig on [0,T] (spacing sig/2), nu_j >= tau, sum nu_j = 1,
# int nu cos(t log m) dt = 0 for 2<=m<=M.  Maximize tau (interior margin, reported as tau*n).
# Tail pollution: max_{M<m<=4M} |nu^(log m)| / nu^(0).
import numpy as np, json, time, mpmath as mp
from scipy.optimize import linprog
from scipy.signal import fftconvolve
from multiprocessing import Pool
TMAX, DT = 400.0, 0.01
def zsq(ts):
    mp.mp.dps = 15
    return np.array([float(mp.siegelz(t))**2 for t in ts])
def run(args):
    M, T, sig, ts, z2 = args; t0 = time.time()
    sel = ts < T; t = ts[sel]; w = z2[sel]*DT
    if sig > 0:
        cs = np.arange(0.0, T + 1e-9, sig/2)
        kt = np.arange(-6*sig, 6*sig + DT/2, DT); ker = np.exp(-kt**2/(2*sig*sig))
        cidx = np.clip(np.round(cs/DT).astype(int), 0, len(t) - 1)
        def proj(f):  # (f * phi)(c_j) = sum_t f(t) phi(t - c_j)
            return fftconvolve(f, ker, mode="same")[cidx]
        Phi = lambda nu: fftconvolve(np.bincount(cidx, weights=nu, minlength=len(t)), ker, mode="same")
    else:
        cell = 0.1; n = int(round(T/cell)); cidx_t = np.minimum((t//cell).astype(int), n - 1)
        proj = lambda f: np.bincount(cidx_t, weights=f, minlength=n)
        Phi = lambda nu: nu[cidx_t]
    lm = np.log(np.arange(2, M + 1))
    I = np.array([proj(w*np.cos(t*l)) for l in lm]); n = I.shape[1]
    I /= np.linalg.norm(I, axis=1, keepdims=True)
    # nu_j = tau + u_j, u_j >= 0:  maximize tau  s.t. I(tau*1 + u) = 0, n*tau + sum u = 1
    A_eq = np.vstack([np.hstack([I, I.sum(axis=1, keepdims=True)]), np.hstack([np.ones((1, n)), [[float(n)]]])])
    b_eq = np.concatenate([np.zeros(len(lm)), [1.0]])
    c = np.zeros(n + 1); c[-1] = -1.0
    res = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)]*n + [(None, None)], method="highs")
    out = dict(M=M, T=T, sig=sig, n=n, status=int(res.status), time=round(time.time() - t0, 1))
    if res.status == 0:
        tau = res.x[-1]; nu = res.x[:n] + tau
        dens = Phi(nu)*z2[sel]
        g0 = np.sum(dens)*DT
        tail = [abs(np.sum(dens*np.cos(t*np.log(m)))*DT)/g0 for m in range(M + 1, 4*M + 1)]
        head = [abs(np.sum(dens*np.cos(t*np.log(m)))*DT)/g0 for m in range(2, M + 1)]
        out.update(tau_n=float("%.4e" % (tau*n)), head_max=float("%.1e" % max(head)), tail_max=float("%.3e" % max(tail)),
                   tail_med=float("%.3e" % np.median(tail)))
    return out
if __name__ == "__main__":
    ts = np.arange(DT/2, TMAX, DT)
    with Pool(8) as pool:
        z2 = np.concatenate(pool.map(zsq, np.array_split(ts, 128)))
    np.save("z2_400.npy", z2)
    tasks = [(M, T, s, ts, z2) for M in (30, 60, 150, 300) for T in (100.0, 400.0) for s in (1.0, 0.5, 0.25, 0.0)]
    with Pool(8) as pool:
        for r in pool.imap_unordered(run, tasks):
            print(json.dumps(r), flush=True)

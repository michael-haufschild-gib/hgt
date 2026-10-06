# (a) Positivity length T_max(M) of mean-zero cosine sums C(t)=sum_{m=2}^M c_m cos(t log m), C(0)=1, C>=0 on [0,T].
#     Montgomery-Vaughan + Hilbert inequality give T_max(M) <= ~10.6 M (linear).
# (b) Stiemke C-PIN test with T proportional to M: nu = Z(t)^2 * h(t), h piecewise constant >= tau on cells,
#     sum nu_j = 1, int nu cos(t log m) dt = 0 for 2<=m<=M. Feasible tau>0 = interior prime-blind exact-null test.
import numpy as np, json, sys, time, mpmath as mp
from scipy.optimize import linprog
from multiprocessing import Pool

def tmax(M):
    lm = np.log(np.arange(2, M + 1))
    def feas(T):
        t = np.arange(0.0, T, 0.25/np.log(M))
        A = -np.cos(np.outer(t, lm))                       # -C(t) <= 0
        res = linprog(np.zeros(len(lm)), A_ub=A, b_ub=np.zeros(len(t)), A_eq=np.ones((1, len(lm))), b_eq=[1.0],
                      bounds=[(-1e4, 1e4)]*len(lm), method="highs")
        return res.status == 0
    lo, hi = 0.5, 4.0
    while feas(hi) and hi < 5e4: lo, hi = hi, 2*hi
    for _ in range(14):
        mid = (lo + hi)/2
        if feas(mid): lo = mid
        else: hi = mid
    return dict(part="a", M=M, Tmax=round(lo, 3), Tmax_over_M=round(lo/M, 4))

def zsq(ts):
    mp.mp.dps = 15
    return np.array([float(mp.siegelz(t))**2 for t in ts])

def stiemke(args):
    M, T, cell = args; t0 = time.time()
    dt = cell/10; ts = np.arange(dt/2, T, dt)
    with Pool(8) as pool:
        chunks = np.array_split(ts, 64); z2 = np.concatenate(pool.map(zsq, chunks))
    ncell = int(round(T/cell)); idx = np.minimum((ts//cell).astype(int), ncell - 1)
    lm = np.log(np.arange(2, M + 1))
    I = np.zeros((len(lm), ncell))
    for k, l in enumerate(lm):
        I[k] = np.bincount(idx, weights=z2*np.cos(ts*l)*dt, minlength=ncell)
    I /= np.linalg.norm(I, axis=1, keepdims=True)
    # variables: nu_1..nu_n, tau ; maximize tau
    n = ncell
    c = np.zeros(n + 1); c[-1] = -1.0
    A_ub = np.hstack([-np.eye(n), np.ones((n, 1))])          # tau - nu_j <= 0
    A_eq = np.vstack([np.hstack([I, np.zeros((len(lm), 1))]), np.hstack([np.ones((1, n)), [[0.0]]])])
    b_eq = np.concatenate([np.zeros(len(lm)), [1.0]])
    res = linprog(c, A_ub=A_ub, b_ub=np.zeros(n), A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)]*n + [(None, None)], method="highs")
    tau = -res.fun if res.status == 0 else None
    return dict(part="b", M=M, T=T, cell=cell, ncell=n, status=int(res.status),
                tau_times_n=(None if tau is None else float("%.4e" % (tau*n))), time=round(time.time() - t0, 1))

if __name__ == "__main__":
    with Pool(5) as pool:
        for r in pool.imap_unordered(tmax, [8, 16, 32, 64, 128]):
            print(json.dumps(r), flush=True)
    for M, T in ((30, 100), (30, 360), (60, 100), (60, 720), (150, 100), (150, 400), (150, 1800)):
        print(json.dumps(stiemke((M, T, 0.1))), flush=True)

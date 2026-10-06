# (N1) via Riemann-kernel translates: f = sum_k b_k Phi(x - log k), fhat = Xi(t) * D(t), D(t) = sum_k b_k k^{it}.
# g = f*f~ :  g(y) = sum_{k,l} X_kl K(y - log(k/l)),  K = Phi*Phi~ (super-exponential decay), X = b b^T (PSD lift).
# For every Weil-positive lam:  int |fhat|^2 dmu_lam = sum_m (Lambda-lam)(m) m^{-1/2} 2 g(log m)  (explicit formula, Xi kills all zeros).
# SDP: max c  s.t. X PSD, g(0)=1, g(log m)=0 for every m whose coefficient row is non-negligible, P(t)=sum X_kl cos(t log(k/l)) >= c on window.
import numpy as np, cvxpy as cp, json, sys, time
from multiprocessing import Pool
xs = np.linspace(-4.0, 4.0, 2**16 + 1); dx = xs[1]-xs[0]
def Phi(x):
    x = np.abs(x)                                   # Phi is even; the series converges fast for x >= 0
    n = np.arange(1, 8)[:, None]; e = np.exp(2*x)[None, :]
    return 2*np.sum((2*np.pi**2*n**4*np.exp(4.5*x)[None, :] - 3*np.pi*n**2*np.exp(2.5*x)[None, :])*np.exp(-np.pi*n**2*e), axis=0)
PH = Phi(xs)
from scipy.signal import fftconvolve
KG = fftconvolve(PH, PH[::-1], mode="full")*dx          # K on lags (i - len+1)*dx
LAG = (np.arange(len(KG)) - (len(PH) - 1))*dx
def K(y):
    return np.interp(np.atleast_1d(y), LAG, KG, left=0.0, right=0.0)
def run(args):
    N, t0, half, eps = args; t1 = time.time()
    lk = np.log(np.arange(1, N + 1))
    R = lk[:, None] - lk[None, :]                      # log(k/l)
    uniq, inv = np.unique(np.round(R, 12), return_inverse=True)
    Ku = {}
    def Kmat(shift):
        vals = K(shift - uniq)
        return vals[inv].reshape(N, N)
    K0 = K(np.array([0.0]))[0]
    rows = []
    for m in range(2, 50*N):
        A = Kmat(np.log(m))
        if np.max(np.abs(A)) < eps*K0:
            if np.log(m) > np.log(N) + 3: break
            continue
        rows.append(A/np.max(np.abs(A)))
    X = cp.Variable((N, N), PSD=True); c = cp.Variable()
    cons = [cp.sum(cp.multiply(Kmat(0.0), X)) == 1]
    cons += [cp.sum(cp.multiply(A, X)) == 0 for A in rows]
    for t in np.linspace(t0 - half, t0 + half, 21):
        cons.append(cp.sum(cp.multiply(np.cos(t*R), X)) >= c)
    p = cp.Problem(cp.Maximize(c), cons)
    try:
        p.solve(solver=cp.CLARABEL, max_iter=3000)
    except Exception:
        try:
            p.solve(solver=cp.SCS, max_iters=20000, eps=1e-9)
        except Exception as e:
            return dict(N=N, t0=t0, eps=eps, status="solver_error")
    Xv = X.value
    if Xv is None:
        return dict(N=N, t0=t0, eps=eps, status=p.status)
    resid = max(abs(np.sum(A*Xv)) for A in rows) if rows else 0.0
    return dict(N=N, t0=t0, eps=eps, nrows=len(rows), status=p.status, c=float("%.4e" % c.value) if c.value is not None else None,
                Xnorm=float("%.3e" % np.abs(Xv).sum()) if Xv is not None else None, max_resid=float("%.1e" % resid),
                eigmin=float("%.1e" % np.linalg.eigvalsh(Xv)[0]) if Xv is not None else None, time=round(time.time()-t1, 1))
if __name__ == "__main__":
    print("int Phi=%.6f (Xi(0)=0.497121)" % (np.sum(PH)*dx), flush=True)
    print("K(0)=%.6e K(log2)=%.3e K(log3)=%.3e K(log4)=%.3e K(log6)=%.3e" % tuple(K(np.log([1, 2, 3, 4, 6]))), flush=True)
    tasks = [(N, t0, 0.5, eps) for eps in (1e-4, 1e-7, 1e-10, 1e-13) for N in (6, 12, 24, 48) for t0 in (17.5, 40.0)]
    with Pool(8) as pool:
        for r in pool.imap_unordered(run, tasks):
            print(json.dumps(r), flush=True)

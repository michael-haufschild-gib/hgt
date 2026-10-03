# Degree-2 abundance threshold: window-local dim of W_2(N) (Gamma_R^2, conductor N, entire part) vs N.
import os; os.environ['OPENBLAS_NUM_THREADS'] = '8'
import numpy as np, json, sys, mpmath as mp
from scipy.linalg import svd
from afe import *
d = int(os.environ.get("DEG", "2")); T1, T2 = float(os.environ.get("T1", "100")), float(os.environ.get("T2", "140"))
Ns = [float(x) for x in sys.argv[1].split(",")]
for Nc in Ns:
    logq = np.log(Nc)
    Tc = T2 + 60; nt = np.sqrt(Nc)*(Tc/(2*np.pi))**(d/2); N = int(np.ceil(4.0*nt)) + 5
    n = np.arange(1, N + 1, dtype=float)
    td = np.arange(0.05, Tc, 0.08)
    D = defect_rows(td, n, d, logq, sigma0=3.0, c1=0.5, c2=2.5)
    A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
    U, s, Vt = svd(A, full_matrices=True); s = s/s[0]; s = np.concatenate([s, np.zeros(N - len(s))])
    B = Vt[s < 1e-8].T
    if B.shape[1] == 0:
        print(json.dumps(dict(N=Nc, ncoef=N, k=0, count={}, sv=[]))); continue
    tw = np.arange(T1, T2, 0.04)
    R = Zrows(tw, n, d, logq, a=0.02) @ B
    sv = np.linalg.svd(R, compute_uv=False)/np.sqrt(len(tw))
    cnt = {th: int(np.sum(sv > th)) for th in (1e-2, 1e-3, 1e-4)}
    print(json.dumps(dict(N=Nc, ncoef=N, k=B.shape[1], count_abs=cnt, sv=[float("%.3g" % x) for x in sv[:12]])), flush=True)

# Window-local freedom density of W_d vs zero density.  For window [T1,T2]: null space of FE defect up to T2+60,
# Z-evaluation on the window; count singular values above thresholds (relative to the window's top value).
import os; os.environ['OPENBLAS_NUM_THREADS'] = '8'
import numpy as np, json, sys, mpmath as mp
from scipy.linalg import svd
from afe import *
d = int(sys.argv[1]); wins = [tuple(float(v) for v in w.split(":")) for w in sys.argv[2].split(",")]
def Nzeta(T): return float(mp.siegeltheta(T)/mp.pi + 1)
for T1, T2 in wins:
    Tc = T2 + 60; nt = (Tc/(2*np.pi))**(d/2); N = int(np.ceil(4.0*nt)) + 5
    n = np.arange(1, N + 1, dtype=float)
    td = np.arange(0.05, Tc, 0.08)
    D = defect_rows(td, n, d, 0.0, sigma0=3.0, c1=0.5, c2=2.5)
    A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
    U, s, Vt = svd(A, full_matrices=True); s = s/s[0]; s = np.concatenate([s, np.zeros(N - len(s))])
    B = Vt[s < 1e-8].T
    tw = np.arange(T1, T2, 0.04)
    R = Zrows(tw, n, d, 0.0, a=0.02) @ B
    sv = np.linalg.svd(R, compute_uv=False)/np.sqrt(len(tw))
    zeros_win = Nzeta(T2) - Nzeta(T1)
    cnt = {th: int(np.sum(sv > th*sv[0])) for th in (0.3, 0.1, 0.03, 0.01, 1e-3)}
    print(json.dumps(dict(d=d, T1=T1, T2=T2, N=N, k=B.shape[1], zeta_zeros=round(zeros_win, 2),
        Lpred=round((d - 2)*zeros_win, 2), count=cnt, ratio_0p1=round(cnt[0.1]/zeros_win/(d-2), 3),
        sv=[float("%.3g" % x) for x in sv[:int(3*zeros_win) + 5]])), flush=True)

# Scaling of the visible W_d dimension on [0,T] (spectrum of Z-evaluation of the FE-null space).
import numpy as np, json, sys, mpmath as mp
from scipy.linalg import svd
from afe import *
d = int(sys.argv[1]); Ts = [float(x) for x in sys.argv[2].split(",")]
for T in Ts:
    Tc = T + 60; nt = (Tc/(2*np.pi))**(d/2); N = int(np.ceil(4.0*nt)) + 5
    n = np.arange(1, N+1, dtype=float)
    td = np.arange(0.05, Tc, 0.08)
    D = defect_rows(td, n, d, 0.0, sigma0=3.0, c1=0.5, c2=2.5)
    A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
    U, s, Vt = svd(A, full_matrices=True); s = s/s[0]
    s = np.concatenate([s, np.zeros(N - len(s))])
    B = Vt[s < 1e-8].T
    tg = np.arange(0.2, T, 0.05)
    R1 = Zrows(tg, n, d, 0.0, a=0.02)
    sv = np.linalg.svd(R1 @ B, compute_uv=False)/np.sqrt(len(tg))
    Nz = float(mp.siegeltheta(T)/mp.pi + 1)
    cnt = {e: int(np.sum(sv > 10.0**-e)) for e in (2, 3, 4, 6)}
    print(json.dumps(dict(d=d, T=T, N=N, k=B.shape[1], Nzeta=round(Nz, 1),
        pred_L399=round((d-2)*(T/(2*np.pi))*(np.log(T/(2*np.pi)) - 1), 1), count=cnt,
        sv=[float("%.2e" % x) for x in sv[:40]])), flush=True)

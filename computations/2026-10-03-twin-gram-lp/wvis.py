# Visible dimension of approximate W on [0,T] vs null-space threshold; AFE weight-independence as W-certificate.
import numpy as np, json, sys
from scipy.linalg import svd
from afe import *
T = 80.0
for d in (2, 3):
    for mult in (4.0, 8.0):
        Tc = T + 60; nt = (Tc/(2*np.pi))**(d/2); N = int(np.ceil(mult*nt)) + 5
        n = np.arange(1, N+1, dtype=float)
        td = np.arange(0.05, Tc, 0.08)
        D = defect_rows(td, n, d, 0.0, sigma0=3.0, c1=0.5, c2=2.5)
        A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
        U, s, Vt = svd(A, full_matrices=True); s = s/s[0]
        s = np.concatenate([s, np.zeros(N - len(s))])
        tg = np.arange(0.2, T, 0.05)
        R1 = Zrows(tg, n, d, 0.0, a=0.02); R2 = Zrows(tg, n, d, 0.0, a=0.05)
        for thr in (1e-9, 1e-7, 1e-5, 1e-3):
            B = Vt[s < thr].T
            if B.shape[1] == 0: print(d, mult, thr, "k=0"); continue
            M1 = R1 @ B; M2 = R2 @ B
            u, sv, vt = np.linalg.svd(M1, full_matrices=False)
            # weight error of each visible direction
            werr = np.linalg.norm(M2 @ vt.T - M1 @ vt.T, axis=0)/np.sqrt(len(tg))
            vis = sv/np.sqrt(len(tg))
            good = int(np.sum((vis > 1e-2) & (werr < 1e-3*np.maximum(vis, 1e-300))))
            print(json.dumps(dict(d=d, mult=mult, N=N, thr=thr, k=B.shape[1], good=good,
                  rms_vis=[float("%.2e" % x) for x in vis[:14]],
                  werr=[float("%.1e" % x) for x in werr[:14]])), flush=True)

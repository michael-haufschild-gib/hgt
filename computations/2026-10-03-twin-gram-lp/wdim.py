# Calibration: numerical dimension of approximate W (entire, Gamma_R^d, q=1) vs truncation N and height T_c.
import numpy as np, time, sys, json
from afe import *
out = []
for d in (1, 2, 3, 4):
    for Tc in (60.0, 120.0):
        nt = (Tc/(2*np.pi))**(d/2)
        for mult in (2.0, 4.0, 8.0):
            N = int(np.ceil(mult*nt)) + 5
            n = np.arange(1, N+1, dtype=float)
            t = np.arange(0.05, Tc, 0.08)
            D = defect_rows(t, n, d, 0.0, sigma0=3.0, c1=0.5, c2=2.5)
            A = np.vstack([D.real, D.imag])
            A /= np.linalg.norm(A, axis=1, keepdims=True)
            A *= np.sqrt(N)  # columns scaled? keep plain; use n^{-3} column weights? no
            sv = np.linalg.svd(A, compute_uv=False)
            sv = sv/sv[0]
            k = {th: int(np.sum(sv < th)) + max(0, N - len(sv)) for th in (1e-6, 1e-9, 1e-12)}
            rec = dict(d=d, Tc=Tc, N=N, nt=round(nt, 1), null=k)
            out.append(rec); print(rec, flush=True)
json.dump(out, open("wdim.json", "w"))

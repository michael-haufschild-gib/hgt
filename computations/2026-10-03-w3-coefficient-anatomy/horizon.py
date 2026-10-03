# S17: low-coefficient rigidity horizon. For unit e with FE-defect ||A e|| <= tau, max mass sum_{n<=n0} e_n^2.
# Via SVD of A: e = V c; defect = ||S c||; maximize ||P_{n0} V c|| s.t. ||S c|| <= tau, ||c||=1  (approx: restrict to right sing. vectors with s_i <= tau)
import os; os.environ['OPENBLAS_NUM_THREADS'] = '8'
import numpy as np, json, sys
from scipy.linalg import svd
from afe import *
d = int(sys.argv[1]); Tcs = [float(x) for x in sys.argv[2].split(",")]
for Tc in Tcs:
    nt = (Tc/(2*np.pi))**(d/2)
    for mult in (4.0, 8.0):
        N = int(np.ceil(mult*nt)) + 5
        n = np.arange(1, N + 1, dtype=float)
        td = np.arange(0.05, Tc, 0.08)
        D = defect_rows(td, n, d, 0.0, sigma0=3.0, c1=0.5, c2=2.5)
        A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
        U, s, Vt = svd(A, full_matrices=True); s = s/s[0]; s = np.concatenate([s, np.zeros(N - len(s))])
        res = {}
        for tau in (1e-10, 1e-8, 1e-6, 1e-4, 1e-2):
            Vk = Vt[s <= tau]          # rows: admissible directions
            row = {}
            for n0 in (2, 5, 10, 20, 30, 40, 60, 100):
                if n0 > N: continue
                Pm = Vk[:, :n0]          # mass at n<=n0 for combination c: ||Pm^T c||
                row[n0] = float("%.2e" % (np.linalg.norm(Pm, 2)**2)) if Vk.shape[0] else 0.0
            res[tau] = row
        print(json.dumps(dict(d=d, Tc=Tc, N=N, mult=mult, maxlowmass=res)), flush=True)

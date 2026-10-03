import numpy as np, time
from afe import *
for N in (3000, 6000, 12000):
    n = np.arange(1, N+1, dtype=float)
    chi = np.array([0, 1, -1, -1, 1])[np.arange(1, N+1) % 5].astype(float)
    def dconv(a, b):
        c = np.zeros(N)
        for i in range(1, N+1):
            if a[i-1] == 0: continue
            c[i-1::i][:N//i] += a[i-1]*b[:N//i]
        return c
    a3 = dconv(dconv(chi, chi), chi)
    td = np.array([0.3, 5, 20, 40, 80, 120, 160])
    for s0, c2 in ((2.0, 1.5), (3.0, 2.5)):
        D = defect_rows(td, n, 3, np.log(125.0), sigma0=s0, c1=0.5, c2=c2)
        nat = np.abs(np.exp(-np.outer(s0 + 1j*td, np.log(n))) @ a3)
        print(N, s0, "rel defect", np.array2string(np.abs(D @ a3)/nat, precision=1))

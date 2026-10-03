# Validate AFE on L(s,chi_5)^3 (d=3, q=125, entire, root number 1).
import numpy as np, mpmath as mp, time
from afe import *
N = 6000
n = np.arange(1, N+1, dtype=float)
chi = np.array([0, 1, -1, -1, 1])[np.arange(1, N+1) % 5].astype(float)
def dconv(a, b):
    c = np.zeros(N)
    for i in range(1, N+1):
        if a[i-1] == 0: continue
        c[i-1::i][:N//i] += a[i-1]*b[:N//i]
    return c
a3 = dconv(dconv(chi, chi), chi)
logq = np.log(125.0)
ts = np.array([3.7, 14.2, 31.5, 57.9, 88.3, 120.1])
for a in (0.02, 0.05, 0.2):
    t0 = time.time()
    R = Zrows(ts, n, 3, logq, a=a)
    Z = R @ a3
    print("a=%.2f time %.1fs" % (a, time.time()-t0))
    for t, z in zip(ts, Z):
        mp.mp.dps = 30
        L = mp.dirichlet(mp.mpc(0.5, t), [0, 1, -1, -1, 1])
        Th = 3*float(mp.siegeltheta(t)) + 0.5*t*float(logq)
        ex = complex(mp.e**(1j*Th)*L**3)
        print("  t=%7.2f  AFE=% .12e  exact=% .12e  (imag %.1e)  rel.err %.1e" % (t, z, ex.real, ex.imag, abs(z-ex.real)/max(1e-300, abs(ex.real))))
# defect of an exact element at sigma0=1.25
td = np.linspace(0.5, 120, 9)
D = defect_rows(td, n, 3, logq)
print("defect |D e|:", np.abs(D @ a3))
print("scale  |sum|a_n| n^-1.25|:", np.sum(np.abs(a3)*n**-1.25))

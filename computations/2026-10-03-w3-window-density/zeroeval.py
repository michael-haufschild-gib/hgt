# S19: is evaluation of W3 at the actual zeta zeros special?  Compare conditioning of the evaluation map on the window's
# plateau subspace at (a) zeta zeros, (b) Gram points, (c) midpoints between zeros, (d) random points.
import os; os.environ['OPENBLAS_NUM_THREADS'] = '8'
import numpy as np, json, sys, mpmath as mp
from scipy.linalg import svd
from afe import *
d = 3; T1, T2 = float(sys.argv[1]), float(sys.argv[2])
Tc = T2 + 60; nt = (Tc/(2*np.pi))**(d/2); N = int(np.ceil(4.0*nt)) + 5
n = np.arange(1, N + 1, dtype=float)
td = np.arange(0.05, Tc, 0.08)
D = defect_rows(td, n, d, 0.0, sigma0=3.0, c1=0.5, c2=2.5)
A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
U, s, Vt = svd(A, full_matrices=True); s = s/s[0]; s = np.concatenate([s, np.zeros(N - len(s))])
B = Vt[s < 1e-8].T
tw = np.arange(T1, T2, 0.04)
Rw = Zrows(tw, n, d, 0.0, a=0.02) @ B
u, sv, vt = np.linalg.svd(Rw, full_matrices=False)
sv = sv/np.sqrt(len(tw))
kp = int(np.sum(sv > 0.01*sv[0]))
P = vt[:kp].T                      # plateau directions (coefficient space), orthonormal
mp.mp.dps = 20
zs = []
k = 1
while True:
    g = float(mp.im(mp.zetazero(k)))
    if g > T2: break
    if g >= T1: zs.append(g)
    k += 1
zs = np.array(zs); m = len(zs)
# Gram points in window
gr = []
j = int(np.ceil(float(mp.siegeltheta(T1))/np.pi))
while True:
    tt = 2*np.pi*np.exp(1 + float(mp.lambertw((j*np.pi + np.pi/8)/(np.pi*float(mp.e))).real))
    for _ in range(30): tt -= (float(mp.siegeltheta(tt)) - j*np.pi)/(0.5*np.log(tt/(2*np.pi)))
    if tt > T2: break
    if tt >= T1: gr.append(tt)
    j += 1
gr = np.array(gr)
mids = (zs[:-1] + zs[1:])/2
rng = np.random.default_rng(3)
def cond_stats(pts):
    M = Zrows(pts, n, d, 0.0, a=0.02) @ B @ P          # pts x kp
    s_ = np.linalg.svd(M, compute_uv=False)
    return dict(npts=len(pts), smin=float("%.3g" % s_[-1]), smax=float("%.3g" % s_[0]),
                s_low=[float("%.3g" % x) for x in s_[-5:]])
out = dict(T1=T1, T2=T2, kp=kp, nzeros=m, zeros=cond_stats(zs), gram=cond_stats(gr), mids=cond_stats(mids))
rnd = [cond_stats(np.sort(rng.uniform(T1, T2, m)))["smin"] for _ in range(20)]
out["random_smin_quantiles"] = [float("%.3g" % q) for q in np.quantile(rnd, [0.05, 0.25, 0.5, 0.75, 0.95])]
# shifted zeros (all zeros shifted by fraction of local spacing)
for f in (0.25, 0.5):
    sp = np.gradient(zs)
    out["shift_%g" % f] = cond_stats(zs + f*sp)
print(json.dumps(out))

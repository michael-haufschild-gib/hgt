# Worst-aperture search for the fixed-pole Weil criterion, zero-sum model (guidance only).
#   m_pm(a) = sum_{gamma>0} 2 (1 +/- cos(2 a gamma - 2 theta)) / |rho|^2,   rho = 1/2 + i gamma, theta = arg rho
#   (even energy / e^a  ~ m_+,  odd energy / e^a ~ m_-, under RH; c0 = sum 2/|rho|^2 = 2 + gamma - log 4pi)
# Questions: how small does min_{a<=A} m_pm(a) get as A grows?  same over prime entries a = log(p)/2?
import numpy as np, math, sys, time, os
from mpmath import mp, zetazero
NZ = 1500
zf = 'zeros_%d.npy' % NZ
if os.path.exists(zf):
    gam = np.load(zf)
else:
    mp.dps = 15
    gam = np.array([float(zetazero(k).imag) for k in range(1, NZ+1)])
    np.save(zf, gam)
w = 2.0/(0.25 + gam**2)                # weights 2/|rho|^2
th = np.arctan2(gam, 0.5)               # arg rho
c0 = 2 + 0.5772156649015329 - math.log(4*math.pi)
tail = c0 - w.sum()
print(f"NZ={NZ} sum w={w.sum():.6f} c0={c0:.6f} tail mass={tail:.2e}", flush=True)
def m_full(a, sign):
    a = np.asarray(a, dtype=np.float64)[:, None]
    return (w[None, :]*(1 + sign*np.cos(2*a*gam[None, :] - 2*th[None, :]))).sum(axis=1)
K = 8  # zeros used in the coarse filter
def coarse(a, sign):
    return (w[None, :K]*(1 + sign*np.cos(2*a[:, None]*gam[None, :K] - 2*th[None, :K]))).sum(axis=1)
# ---- continuous apertures ----
records = {}
for sign, name in [(+1, 'even'), (-1, 'odd')]:
    best = []  # (value, a)
    step = 2.5e-4
    for A0 in [0, 1e2, 1e3, 1e4, 1e5]:
        A1 = {0:1e2, 1e2:1e3, 1e3:1e4, 1e4:1e5, 1e5:1e6}[A0]
        chunk = 4_000_000
        cand_a, cand_v = [], []
        for s0 in np.arange(A0, A1, chunk*step):
            a = s0 + step*np.arange(min(chunk, int((A1-s0)/step)+1))
            v = coarse(a, sign)
            idx = np.argpartition(v, 200)[:200]
            cand_a.append(a[idx]); cand_v.append(v[idx])
        cand_a = np.concatenate(cand_a); 
        # refine with all zeros around each candidate
        fine = []
        for ac in cand_a:
            aa = ac + np.linspace(-step, step, 41)
            vv = m_full(aa, sign)
            j = np.argmin(vv); fine.append((vv[j], aa[j]))
        fine.sort()
        best_here = fine[0]
        print(f"{name}: A in [{A0:.0e},{A1:.0e}]  min m = {best_here[0]:.5f} (rel {best_here[0]/c0:.4f}) at a = {best_here[1]:.6f}; next: " + ", ".join(f"{v:.5f}@{a:.3f}" for v,a in fine[1:4]), flush=True)
        records[(name, A1)] = best_here
# ---- prime entries a = log(p)/2 ----
N = 10**8
sieve = np.ones(N+1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0]
print(f"primes up to {N}: {len(primes)}", flush=True)
ap = 0.5*np.log(primes.astype(np.float64))
for sign, name in [(-1, 'odd'), (+1, 'even')]:
    vals = []
    for s0 in range(0, len(ap), 2_000_000):
        vals.append(coarse(ap[s0:s0+2_000_000], sign))
    vals = np.concatenate(vals)
    idx = np.argpartition(vals, 300)[:300]
    full = m_full(ap[idx], sign)
    order = np.argsort(full)
    print(f"{name} at prime entries p<=1e8: smallest margins:")
    for j in order[:8]:
        print(f"   p={primes[idx[j]]}: m={full[j]:.5f} (rel {full[j]/c0:.4f})", flush=True)
    # record minima by prime size
    for P in [10**4, 10**5, 10**6, 10**7, 10**8]:
        sel = primes[idx] <= P
        if sel.any(): print(f"   min over p<={P:.0e}: {full[sel].min():.5f} (rel {full[sel].min()/c0:.4f})", flush=True)
print("done")

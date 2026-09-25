"""Rigidity of the prime kinks under positive-definiteness of the lag function.

Phi(L) = arch(L) + sum_{n<=e^L} 2 Lambda(n) n^{-1/2} sinh((L - log n)/2)   (even extension)
RH <=> Phi positive definite.  Perturb ONE prime power n0: shift its kink position log n0 -> log n0 + eps,
or scale its weight by (1+eps); all other prime powers exact.  Find the largest |eps| keeping the
Toeplitz matrix of Phi on a grid of [0, L] positive semidefinite.  Baseline: min eigenvalue of the
unperturbed prime-side Phi (should be >= 0 under RH; its size is the PD margin).
"""
import numpy as np, sys, json, time
from multiprocessing import Pool
from scipy.linalg import toeplitz, eigvalsh

EULER = 0.57721566490153286060651209
C0 = 2 + EULER - np.log(4*np.pi)

def prime_powers(limit):
    out = []
    sieve = np.ones(limit+1, dtype=bool); sieve[:2] = False
    for i in range(2, int(limit**0.5)+1):
        if sieve[i]: sieve[i*i::i] = False
    for p in np.nonzero(sieve)[0]:
        q = int(p)
        while q <= limit:
            out.append((q, np.log(p)))
            q *= p
    out.sort()
    return out

def arch(L):
    L = np.asarray(L, dtype=float)
    X = np.exp(L)
    with np.errstate(divide='ignore', invalid='ignore'):
        B = np.log(2*np.pi) - 1 + 0.5*np.log1p(-X**-2) + X*np.arctanh(1.0/X)
        val = np.exp(L/2)*(1+EULER-L) - np.exp(-L/2)*B
    return np.where(L < 1e-12, C0, val)

def phi_pert(L, pps, n0=None, shift=0.0, scale=1.0):
    L = np.abs(np.asarray(L, dtype=float))
    val = arch(L)
    for n, lp in pps:
        ln = np.log(n); w = 2*lp*n**-0.5
        if n == n0:
            ln = ln + shift; w = w*scale
        mask = L >= ln
        if mask.any():
            val = val + np.where(mask, w*np.sinh((L-ln)/2), 0.0)
    return val

def min_eig(L, n, **kw):
    grid = np.linspace(0, L, n)
    return eigvalsh(toeplitz(phi_pert(grid, PPS, **kw)), subset_by_index=[0,0])[0]

def tolerance(n0, kind, sign, L, n, tol):
    """largest eps>0 (in direction sign) with min eigenvalue >= -tol."""
    def ok(e):
        kw = dict(n0=n0, shift=sign*e) if kind == 'shift' else dict(n0=n0, scale=1+sign*e)
        return min_eig(L, n, **kw) >= -tol
    lo, hi = 0.0, 1e-4
    while ok(hi) and hi < 4.0:
        lo, hi = hi, hi*2
    if hi >= 4.0 and ok(hi): return hi, 'unbounded'
    for _ in range(30):
        mid = 0.5*(lo+hi)
        if ok(mid): lo = mid
        else: hi = mid
    return 0.5*(lo+hi), 'ok'

def job(args):
    n0, L, n, tol = args
    t = time.time()
    out = dict(n0=n0, L=L)
    for kind in ('shift', 'scale'):
        for sign, name in ((+1, 'plus'), (-1, 'minus')):
            v, st = tolerance(n0, kind, sign, L, n, tol)
            out[f'{kind}_{name}'] = float(v); out[f'{kind}_{name}_status'] = st
    out['secs'] = time.time()-t
    return out

PPS = prime_powers(int(np.exp(9.0))+2)

if __name__ == "__main__":
    n = 500
    print("baseline min eigenvalue of Toeplitz(Phi) on [0,L], grid", n)
    base = {}
    for L in (1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0):
        m = min_eig(L, n); base[L] = float(m)
        print(f"  L={L:4.1f}  min eig = {m: .3e}   (c0 = {C0:.4f})")
    sys.stdout.flush()
    tol = 1e-10
    L = 6.0
    n0s = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32]
    with Pool(16) as pool:
        res = pool.map(job, [(n0, L, n, tol) for n0 in n0s])
    print(f"\nPD tolerances on [0,{L}] (grid {n}); shift = kink position log n0 -> log n0 +/- eps; scale = weight*(1 +/- eps)")
    print("  n0   w=2Lam/sqrt(n0)   shift+     shift-     scale+     scale-")
    for r in res:
        n0 = r['n0']; lam = [lp for (q,lp) in PPS if q == n0][0]; w = 2*lam*n0**-0.5
        print(f"{n0:4d}   {w:8.4f}      {r['shift_plus']:.5f}   {r['shift_minus']:.5f}   {r['scale_plus']:.5f}   {r['scale_minus']:.5f}  {r['secs']:.0f}s")
    json.dump(dict(baseline=base, tolerances=res), open('pd_rigidity.json','w'), indent=1)

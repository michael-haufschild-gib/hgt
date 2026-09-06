"""Positive-definiteness horizon of the prime-truncated lag function.

Phi(L) = sum_rho e^{L(rho-1/2)}/(rho(1-rho))  (absolutely convergent, even, Phi(0)=2+gamma-log 4pi)
Prime side (L>0, X=e^L):
  Phi(L) = e^{-L/2}(X - psi(X)) + e^{L/2}(sum_{n<=X} Lambda(n)/n - L + gamma) - e^{-L/2} B(X)
  B(X)   = log(2pi) - 1 + (1/2) log(1 - X^{-2}) + X artanh(1/X)
  = arch(L) + sum_{n<=X} 2 Lambda(n) n^{-1/2} sinh((L - log n)/2)
  arch(L)= e^{L/2}(1+gamma-L) - e^{-L/2} B(e^L)
Phi_P: keep only prime powers n <= P.  RH  <=>  Phi positive definite  <=>  |Phi| <= Phi(0).
Question: L*(P) = largest L with Phi_P positive definite on [-L, L] (Toeplitz test on a grid), versus log(next prime power).
"""
import numpy as np, sys, json, time
from multiprocessing import Pool

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

def phi_trunc(L, pps):
    """Phi with prime powers in pps (list of (n, log p)) included; even extension."""
    L = np.abs(np.asarray(L, dtype=float))
    val = arch(L)
    for n, lp in pps:
        ln = np.log(n)
        mask = L >= ln
        if mask.any():
            val = val + np.where(mask, 2*lp*n**-0.5*np.sinh((L-ln)/2), 0.0)
    return val

def zero_side(L, gammas):
    L = np.asarray(L, dtype=float)
    return np.array([np.sum(2*np.cos(g*L_)/(0.25+g*g)) for L_ in L for g in [gammas]])

def min_eig_toeplitz(fvals):
    from scipy.linalg import toeplitz, eigvalsh
    T = toeplitz(fvals)
    return eigvalsh(T, subset_by_index=[0,0])[0]

def horizon(pps, Lmax=14.0, n=300, tol=-1e-9):
    """Largest L such that Toeplitz(Phi_P on grid [0,L]) is PSD; bisection after coarse scan."""
    def ok(L):
        grid = np.linspace(0, L, n)
        return min_eig_toeplitz(phi_trunc(grid, pps)) >= tol*max(1.0, L)
    # coarse scan
    Ls = np.arange(0.2, Lmax+1e-9, 0.2)
    bad = None
    for L in Ls:
        if not ok(L):
            bad = L; break
    if bad is None:
        return Lmax, False
    lo, hi = bad-0.2, bad
    for _ in range(25):
        mid = 0.5*(lo+hi)
        if ok(mid): lo = mid
        else: hi = mid
    return 0.5*(lo+hi), True

def sup_horizon(pps, Lmax=14.0):
    """Largest L with |Phi_P| <= Phi(0) on [0, L] (the 2x2 minors)."""
    grid = np.linspace(0, Lmax, 140001)
    v = phi_trunc(grid, pps)
    bad = np.nonzero(np.abs(v) > C0 + 1e-12)[0]
    return (grid[bad[0]] if len(bad) else Lmax), (len(bad) > 0)

def job(args):
    P, allpps, Lmax = args
    pps = [q for q in allpps if q[0] <= P]
    nxt = [q for q in allpps if q[0] > P]
    ln_next = np.log(nxt[0][0]) if nxt else float('nan')
    t = time.time()
    Lstar, found = horizon(pps, Lmax=Lmax)
    Lsup, found2 = sup_horizon(pps, Lmax=Lmax)
    return dict(P=P, log_next=float(ln_next), L_pd=float(Lstar), pd_found=bool(found),
                slack_pd=float(Lstar-ln_next), L_sup=float(Lsup), sup_found=bool(found2),
                slack_sup=float(Lsup-ln_next), secs=time.time()-t)

if __name__ == "__main__":
    Lmax = 14.0
    allpps = prime_powers(int(np.exp(Lmax))+2)
    gam = np.load('/root/weil/zeros_1500.npy')
    # sanity: prime-side formula vs zero side (true Phi, all prime powers <= e^L)
    Ls = np.array([0.0, 0.3, 0.69, 0.7, 1.0, 1.5, 2.0, 3.0, 4.0, 5.0, 6.0, 8.0, 10.0, 12.0])
    ps = phi_trunc(Ls, allpps)
    zs = zero_side(Ls, gam)
    print("L, prime-side Phi, zero-side Phi (1500 zeros), diff")
    for a,b,c in zip(Ls, ps, zs): print(f"{a:6.2f} {b: .6f} {c: .6f} {b-c: .2e}")
    print("Phi(0) = c0 =", C0, " zero side partial:", np.sum(2/(0.25+gam*gam)))
    sys.stdout.flush()
    Ps = [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64, 67, 71, 73, 79, 81, 83, 89, 97, 101, 128, 256, 512, 1024, 2048]
    with Pool(16) as pool:
        res = pool.map(job, [(P, allpps, Lmax) for P in Ps])
    print("\nP  log(next)  L_pd  slack_pd | L_sup slack_sup")
    for r in res:
        print(f"{r['P']:5d} {r['log_next']:8.4f} {r['L_pd']:8.4f} {r['slack_pd']:+8.4f} | {r['L_sup']:8.4f} {r['slack_sup']:+8.4f}  {'' if r['pd_found'] else '(PD to Lmax)'} {r['secs']:.0f}s")
    json.dump(res, open('pd_horizon.json','w'), indent=1)

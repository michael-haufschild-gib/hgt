#!/usr/bin/env python3
"""(FLOOR) probe — doc 84 §5. Pre-registered in prereg2 block below (binds).

Measures, in the Steinhaus model at theta = 1/2:
 F1: the slice field-energy w = sum_{p in (N^{3/4}, N]} |mu_p(X)|^2 / p
     distribution near 0: exponent of P(w <= u) as u -> 0.
 F2: spectrum of the PSD form T (w = <X, T X> over the k-basis):
     effective rank / eigenvalue decay (deterministic, per N).
 F3: cascade-level small-ball exponents: the objects P_inf (level 0),
     mu_p common field at p ~ N (level 1 ~ M_y-type), and the level-2 band
     object; 2D-density flatness Q(t)/t^2 for each.

PREREG2 (before run):
 - F1 (prior 0.6): log-log slope of P(w <= u) on the measurable range
   in [1, 2] at every N in {400, 1000, 4000}; i.e. P(w<=u) <= C*u^1
   (kappa = 2, rank-1-dominated) — NOT below 0.8 (kappa < 1.6 would
   refute even the log-lossy closure).
 - F2 (prior 0.5): second eigenvalue lam2 >= 0.10*lam1 at every N
   (eigen-spread present); FALSIFIER: lam2/lam1 -> 0 with N (pure rank-1).
 - F3 (prior 0.7): all measured levels have Q(t)/t^2 flat within factor 3
   over t in [0.1, 0.5] (bounded 2D density at every level — (FLOOR)
   TRUE-shaped down the cascade).
"""
import numpy as np, json, math, time, sys

SEED = (1111089585816317988 // 7) % (2**32)
rng = np.random.default_rng(SEED)
OUT = {}

def mu_sieve(y):
    mu = np.ones(y + 1, dtype=int); primes = []
    is_c = np.zeros(y + 1, dtype=bool)
    for i in range(2, y + 1):
        if not is_c[i]: primes.append(i); mu[i] = -1
        for p in primes:
            if i * p > y: break
            is_c[i * p] = True
            mu[i * p] = 0 if i % p == 0 else -mu[i]
            if i % p == 0: break
    mu[0] = 0
    return mu

def mollifier(N):
    y = int(round(N ** 0.5)); y1 = max(2, int(round(y ** 0.5)))
    mu = mu_sieve(y); lam = mu.astype(float)
    for d in range(y1 + 1, y + 1):
        lam[d] *= math.log(y / d) / math.log(y / y1) if d < y else 0.0
    return y, y1, lam

def conv_coeffs(N, y, lam):
    c = np.zeros(N * y + 1)
    for d in range(1, y + 1):
        if lam[d] == 0.0: continue
        c[d::d][: N] += lam[d]
    return c

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i:: i] = False
    return np.nonzero(s)[0]

def spf_sieve(n):
    spf = np.zeros(n + 1, dtype=np.int64)
    for i in range(2, n + 1):
        if spf[i] == 0: spf[i:: i][spf[i:: i] == 0] = i
    return spf

def X_block(B, upto, spf, ps, pidx):
    Xp = np.exp(2j * math.pi * rng.random((B, len(ps))))
    X = np.ones((B, upto + 1), dtype=complex)
    for n in range(2, upto + 1):
        p = spf[n]
        X[:, n] = X[:, n // p] * Xp[:, pidx[int(p)]]
    return X

def run_N(N, ndraw=60000):
    y, y1, lam = mollifier(N)
    c = conv_coeffs(N, y, lam)
    Ny = N * y
    spf = spf_sieve(Ny); ps = primes_upto(Ny)
    pidx = {int(p): i for i, p in enumerate(ps)}
    slice_ps = [int(p) for p in primes_upto(N) if p > N ** 0.75]
    # per slice prime: companion lists
    comp = {}
    for p in slice_ps:
        ks = np.arange(1, Ny // p + 1)
        wk = c[p * ks]; nz = wk != 0
        comp[p] = (ks[nz], wk[nz] / np.sqrt(ks[nz]))
    # T matrix over k-basis (union of companions)
    kall = sorted(set().union(*[set(map(int, comp[p][0])) for p in slice_ps]))
    kmap = {k: i for i, k in enumerate(kall)}
    T = np.zeros((len(kall), len(kall)))
    for p in slice_ps:
        ks, wk = comp[p]
        v = np.zeros(len(kall)); v[[kmap[int(k)] for k in ks]] = wk
        T += np.outer(v, v) / p
    ev = np.linalg.eigvalsh(T)[::-1]
    # Monte Carlo: w and level objects
    m_all = np.nonzero(c)[0]; m_all = m_all[m_all >= 1]
    w_full = c[m_all] / np.sqrt(m_all)
    ws = []; P0 = []; L1 = []; L2 = []
    ptop = slice_ps[-1]
    ks1, wk1 = comp[ptop]                      # level-1 object ~ mu_ptop
    # level-2: band object of level-1: k >= 2 part restricted below y
    band = [(int(k), wkv) for k, wkv in zip(ks1, wk1) if k >= 2]
    B = 400
    kmax_needed = Ny
    for b in range(0, ndraw, B):
        X = X_block(min(B, ndraw - b), kmax_needed, spf, ps, pidx)
        P0.append(np.abs(X[:, m_all] @ w_full))
        wv = np.zeros(X.shape[0])
        for p in slice_ps:
            ks, wk = comp[p]
            mu = X[:, ks] @ wk
            wv += np.abs(mu) ** 2 / p
        ws.append(wv)
        L1.append(np.abs(X[:, ks1] @ wk1))
        if band:
            kb = np.array([k for k, _ in band]); wb = np.array([v for _, v in band])
            L2.append(np.abs(X[:, kb] @ wb))
    w = np.concatenate(ws); P0 = np.concatenate(P0); L1 = np.concatenate(L1)
    L2 = np.concatenate(L2) if L2 else np.array([1.0])
    wn = w / np.mean(w)
    us = np.array([0.02, 0.05, 0.1, 0.2, 0.4, 0.8])
    Pw = [(wn <= u).mean() for u in us]
    fit = [(u, q) for u, q in zip(us, Pw) if q > 0]
    slope = float(np.polyfit(np.log([u for u, _ in fit]), np.log([q for _, q in fit]), 1)[0]) if len(fit) >= 3 else None
    ts = np.array([0.1, 0.2, 0.3, 0.5])
    def dens(A):
        A = A / np.sqrt(np.mean(A ** 2))
        return [float((A <= t).mean() / t ** 2) for t in ts]
    out = dict(N=N, nslice=len(slice_ps), dimT=len(kall),
               ev=[float(e) for e in ev[:6]], ev_ratio=float(ev[1] / ev[0]),
               us=us.tolist(), Pw=[float(q) for q in Pw], slope_w=slope,
               dens_P0=dens(P0), dens_L1=dens(L1), dens_L2=dens(L2),
               Ew=float(np.mean(w)))
    print(f"N={N}: slice={len(slice_ps)}p dimT={len(kall)} "
          f"ev[:4]={['%.3f' % e for e in ev[:4]]} ev2/ev1={out['ev_ratio']:.3f}")
    print(f"  P(w/Ew<=u)={['%.1e' % q for q in Pw]} slope={slope}")
    print(f"  Q/t^2 P0={['%.2f' % v for v in out['dens_P0']]} "
          f"L1={['%.2f' % v for v in out['dens_L1']]} L2={['%.2f' % v for v in out['dens_L2']]}")
    sys.stdout.flush()
    return out

t0 = time.time()
OUT['runs'] = [run_N(N) for N in (400, 1000, 4000)]
OUT['runtime_s'] = time.time() - t0
with open('computations/mwm_kbdd/probe_floor.json', 'w') as f:
    json.dump(OUT, f, indent=1)
print(f"done in {OUT['runtime_s']:.0f}s")

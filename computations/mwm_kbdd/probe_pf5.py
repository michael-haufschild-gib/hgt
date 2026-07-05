#!/usr/bin/env python3
"""P-F5 (doc 84 §9, registered) — normalized-density N-scan + theta-scan of V_bd.
Saturation vs loglog for the NORMALIZED P0 and L1 densities."""
import numpy as np, math, json, sys, time

SEED = (1111089585816317988 // 13) % (2**32)
rng = np.random.default_rng(SEED)

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

def coeffs(N, theta=0.5):
    y = max(3, int(round(N ** theta))); y1 = max(2, int(round(y ** 0.5)))
    mu = mu_sieve(y); lam = mu.astype(float)
    for d in range(y1 + 1, y + 1):
        lam[d] *= math.log(y / d) / math.log(y / y1) if d < y else 0.0
    Ny = N * y
    b = np.zeros(Ny + 1)
    for d in range(1, y + 1):
        if lam[d] == 0.0: continue
        b[d::d][: N] += lam[d]
    return y, b

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

# theta-scan of V_boundary (deterministic, escape E5)
print("theta-scan of V_bd:")
for theta in (0.25, 0.5):
    for N in (10000, 100000):
        y, b = coeffs(N, theta)
        m = np.arange(2, N * y + 1)
        w = b[2:] ** 2 / m
        vbd = float(w[N - 1:].sum()); vin = float(w[: N - 1].sum())
        print(f"  theta={theta} N={N}: V={vin+vbd:.3f} V_bd={vbd:.3f}")
        sys.stdout.flush()

# normalized-density scan (Monte Carlo)
def dens_scan(N, ndraw):
    y, b = coeffs(N)
    Ny = N * y
    m = np.nonzero(b)[0]; m = m[m >= 1]
    w = b[m] / np.sqrt(m)
    spf = spf_sieve(Ny); ps = primes_upto(Ny)
    pidx = {int(p): i for i, p in enumerate(ps)}
    vals = []
    B = max(1, min(200, ndraw // 20))
    for bb in range(0, ndraw, B):
        nb = min(B, ndraw - bb)
        Xp = np.exp(2j * math.pi * rng.random((nb, len(ps))))
        X = np.ones((nb, Ny + 1), dtype=complex)
        for n in range(2, Ny + 1):
            p = spf[n]
            X[:, n] = X[:, n // p] * Xp[:, pidx[int(p)]]
        vals.append(np.abs(X[:, m] @ w))
    A = np.concatenate(vals)
    A = A / np.sqrt(np.mean(A ** 2))
    out = {t: float((A <= t).mean() / t ** 2) for t in (0.2, 0.3, 0.5)}
    print(f"N={N} (ndraw={ndraw}): normalized dens P0 = "
          + str({t: round(v, 3) for t, v in out.items()}))
    sys.stdout.flush()
    return out

t0 = time.time()
RES = {}
for N, nd in ((1000, 60000), (4000, 40000), (16000, 16000), (40000, 8000)):
    RES[N] = dens_scan(N, nd)
Ns = sorted(RES)
for t in (0.2, 0.3, 0.5):
    V = [RES[n][t] for n in Ns]
    x1 = [1 / math.log(n) for n in Ns]; x2 = [math.log(math.log(n)) for n in Ns]
    f1 = np.polyfit(x1, V, 1); r1 = float(np.sqrt(np.mean((np.polyval(f1, x1) - V) ** 2)))
    f2 = np.polyfit(x2, V, 1); r2 = float(np.sqrt(np.mean((np.polyval(f2, x2) - V) ** 2)))
    print(f"t={t}: saturation a={f1[1]:.3f} rms={r1:.4f} | loglog slope={f2[0]:.3f} rms={r2:.4f} "
          f"-> {'SAT' if r1 < r2 else 'LOGLOG'}")
json.dump({str(k): v for k, v in RES.items()}, open('computations/mwm_kbdd/probe_pf5.json', 'w'), indent=1)
print(f"done in {time.time()-t0:.0f}s")

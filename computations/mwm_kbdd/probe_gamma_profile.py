#!/usr/bin/env python3
"""(GAMMA-PROFILE) — deterministic E|gamma_p|^2 vs p (doc 84 §10 item 1).
Exact: E|gamma_p|^2 = sum_{k>=2} c^{(p)}_k^2 / k,
c^{(p)}_k = sum_{e|k, e<=y, k/e <= N/p} lam_e. PREREG-3 binds.
"""
import numpy as np, json, math, sys

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

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i:: i] = False
    return np.nonzero(s)[0]

def lam_variant(N, kind):
    y = int(round(N ** 0.5))
    mu = mu_sieve(y); lam = mu.astype(float)
    if kind == 'sharp':
        return y, lam
    frac = {'bv': 0.5, 'bv25': 0.25, 'bv75': 0.75}[kind]
    y1 = max(2, int(round(y ** frac)))
    for d in range(y1 + 1, y + 1):
        lam[d] *= math.log(y / d) / math.log(y / y1) if d < y else 0.0
    return y, lam

def gamma_profile(N, kind, nprobe=60):
    y, lam = lam_variant(N, kind)
    Ny = N * y
    pr = primes_upto(N)
    large = pr[pr > y]
    idx = np.unique(np.geomspace(1, len(large), nprobe).astype(int) - 1)
    out = []
    # divisor-precompute: for each k up to Ny/y (max band), divisors with lam!=0
    for i in idx:
        p = int(large[i])
        kmax = Ny // p
        var = 0.0
        for k in range(2, kmax + 1):
            s = 0.0
            lim = N // p  # k/e <= N/p  <=>  e >= k/(N/p)
            for e in range(1, min(y, k) + 1):
                if k % e == 0 and lam[e] != 0.0 and k <= lim * e:
                    s += lam[e]
            var += s * s / k
        out.append((p, var))
    return out

def summarize(N, kind):
    prof = gamma_profile(N, kind)
    # dyadic ranges in log p / log N
    alphas = [math.log(p) / math.log(N) for p, _ in prof]
    print(f"N={N} {kind}:")
    for lo, hi in [(0.5, 0.55), (0.55, 0.6), (0.6, 0.65), (0.65, 0.7),
                   (0.7, 0.75), (0.75, 0.8), (0.8, 0.85), (0.85, 0.9),
                   (0.9, 0.95), (0.95, 1.0)]:
        vals = [v for (p, v), a in zip(prof, alphas) if lo <= a < hi]
        if vals:
            print(f"  alpha [{lo:.2f},{hi:.2f}): mean E|g|^2 = {np.mean(vals):.3f}  (n={len(vals)})")
    sys.stdout.flush()
    return prof

RES = {}
for N in (1000, 4000, 40000):
    for kind in (['bv', 'sharp'] if N < 40000 else ['bv', 'sharp', 'bv25', 'bv75']):
        RES[f"{N}:{kind}"] = summarize(N, kind)

with open('computations/mwm_kbdd/probe_gamma_profile.json', 'w') as f:
    json.dump({k: v for k, v in RES.items()}, f, indent=1)
print("done")

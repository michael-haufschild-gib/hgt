#!/usr/bin/env python3
"""P-F7 — V(N) drift, inner/boundary split. Deterministic. PREREG-4 binds."""
import numpy as np, math, json, sys

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

def V_split(N):
    y = int(round(N ** 0.5)); y1 = max(2, int(round(y ** 0.5)))
    mu = mu_sieve(y); lam = mu.astype(float)
    for d in range(y1 + 1, y + 1):
        lam[d] *= math.log(y / d) / math.log(y / y1) if d < y else 0.0
    Ny = N * y
    b = np.zeros(Ny + 1)
    for d in range(1, y + 1):
        if lam[d] == 0.0: continue
        b[d::d][: N] += lam[d]
    m = np.arange(1, Ny + 1)
    w = b[1:] ** 2 / m
    w[0] = 0.0  # exclude m = 1
    Vin = float(w[: N - 1].sum() + w[N - 1])   # m <= N
    Vbd = float(w[N:].sum())                    # m in (N, Ny]
    return Vin, Vbd

res = {}
for N in (1000, 3000, 10000, 30000, 100000):
    vin, vbd = V_split(N)
    res[N] = (vin, vbd)
    print(f"N={N}: V={vin+vbd:.4f}  inner={vin:.4f}  boundary={vbd:.4f}  loglogN={math.log(math.log(N)):.3f}")
    sys.stdout.flush()

Ns = sorted(res)
V = [sum(res[n]) for n in Ns]
x1 = [1 / math.log(n) for n in Ns]
x2 = [math.log(math.log(n)) for n in Ns]
f1 = np.polyfit(x1, V, 1); r1 = np.sqrt(np.mean((np.polyval(f1, x1) - V) ** 2))
f2 = np.polyfit(x2, V, 1); r2 = np.sqrt(np.mean((np.polyval(f2, x2) - V) ** 2))
print(f"saturation fit V = {f1[1]:.3f} + {f1[0]:.3f}/logN,  rms={r1:.4f}")
print(f"logloggrowth  V = {f2[1]:.3f} + {f2[0]:.3f}*loglogN, rms={r2:.4f}")
print(f"VERDICT: {'SATURATION (Branch A)' if r1 < r2 else 'LOGLOG GROWTH (Branch B)'}; boundary shares: "
      + str([f"{res[n][1]/sum(res[n]):.2f}" for n in Ns]))
json.dump({str(k): v for k, v in res.items()}, open('computations/mwm_kbdd/probe_vdrift.json', 'w'), indent=1)

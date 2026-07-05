#!/usr/bin/env python3
"""P-F5 (continued) — normalized-density N-scan via sparse support truncation.
Keeps the top-mass support terms (>= 99.7% of sum b_m^2/m), assembles X(m)
through a sparse prime-exponent matrix. Registration unchanged (PREREG, doc 84 §9/§11)."""
import numpy as np, math, json, sys, time
from scipy import sparse

SEED = (1111089585816317988 // 17) % (2**32)
rng = np.random.default_rng(SEED)

def mu_sieve(y):
    mu = np.ones(y + 1, dtype=np.int64); primes = []
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

def coeffs(N):
    y = int(round(N ** 0.5)); y1 = max(2, int(round(y ** 0.5)))
    mu = mu_sieve(y); lam = mu.astype(float)
    for d in range(y1 + 1, y + 1):
        lam[d] *= math.log(y / d) / math.log(y / y1) if d < y else 0.0
    Ny = N * y
    b = np.zeros(Ny + 1)
    for d in range(1, y + 1):
        if lam[d] == 0.0: continue
        b[d::d][: N] += lam[d]
    return y, b

def dens_scan(N, ndraw, keep_frac=0.997):
    t0 = time.time()
    y, b = coeffs(N)
    Ny = N * y
    m_all = np.nonzero(b)[0]; m_all = m_all[m_all >= 1]
    w_all = b[m_all] / np.sqrt(m_all)
    mass = w_all ** 2
    order = np.argsort(-mass)
    cum = np.cumsum(mass[order])
    K = int(np.searchsorted(cum, keep_frac * cum[-1])) + 1
    sel = order[:K]
    m = m_all[sel].astype(np.int64); w = w_all[sel]
    # sparse prime-exponent matrix for kept m
    spf = np.zeros(Ny + 1, dtype=np.int32)
    for i in range(2, int(Ny ** 0.5) + 1):
        if spf[i] == 0: spf[i * i:: i][spf[i * i:: i] == 0] = i
    # primes: spf[p] == 0 for p > sqrt(Ny)
    rows, cols, vals = [], [], []
    pindex = {}
    for j, mm in enumerate(m):
        n = int(mm)
        while n > 1:
            p = int(spf[n]) if spf[n] != 0 else n
            e = 0
            while n % p == 0: n //= p; e += 1
            idx = pindex.setdefault(p, len(pindex))
            rows.append(j); cols.append(idx); vals.append(e)
    E = sparse.csr_matrix((vals, (rows, cols)), shape=(len(m), len(pindex)))
    npr = len(pindex)
    print(f"N={N}: support {len(m_all)} -> kept {K} ({100*keep_frac:.1f}% mass), "
          f"primes {npr}, prep {time.time()-t0:.0f}s"); sys.stdout.flush()
    vals_out = []
    B = 500
    ET = E.T.tocsr()
    for bb in range(0, ndraw, B):
        nb = min(B, ndraw - bb)
        ph = 2 * math.pi * rng.random((nb, npr))
        phase_m = ph @ ET.T.toarray().T if False else (E @ ph.T).T  # (nb, len(m))
        vals_out.append(np.abs(np.exp(1j * phase_m) @ w))
    A = np.concatenate(vals_out)
    A = A / np.sqrt(np.mean(A ** 2))
    out = {t: float((A <= t).mean() / t ** 2) for t in (0.2, 0.3, 0.5)}
    print(f"N={N} (ndraw={ndraw}): normalized dens P0 = "
          + str({t: round(v, 3) for t, v in out.items()})
          + f"  [{time.time()-t0:.0f}s]")
    sys.stdout.flush()
    return out

RES = {}
for N, nd in ((4000, 40000), (16000, 25000), (40000, 15000), (100000, 8000)):
    RES[N] = dens_scan(N, nd)
Ns = sorted(RES)
print("\n==== P-F5 ADJUDICATION ====")
for t in (0.2, 0.3, 0.5):
    V = [RES[n][t] for n in Ns]
    x1 = [1 / math.log(n) for n in Ns]; x2 = [math.log(math.log(n)) for n in Ns]
    f1 = np.polyfit(x1, V, 1); r1 = float(np.sqrt(np.mean((np.polyval(f1, x1) - V) ** 2)))
    f2 = np.polyfit(x2, V, 1); r2 = float(np.sqrt(np.mean((np.polyval(f2, x2) - V) ** 2)))
    print(f"t={t}: sat a={f1[1]:.3f} rms={r1:.4f} | loglog slope={f2[0]:.3f} rms={r2:.4f} "
          f"-> {'SAT' if r1 < r2 else 'LOGLOG'}")
json.dump({str(k): v for k, v in RES.items()}, open('computations/mwm_kbdd/probe_pf5b.json', 'w'), indent=1)
print("done")

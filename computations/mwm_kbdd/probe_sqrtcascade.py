#!/usr/bin/env python3
"""P-F4 — the sqrt-cascade's load-bearing prediction (doc 84 §7, registered).

Two mutually pair-free slices at theta = 1/2:
  S1 = (N^{15/16}, N],  S2 = (N^{9/16}, N^{5/8}].
w_i = sum_{p in S_i} |mu_p(X)|^2 / p in the Steinhaus model.
Registered: log-log slope of P(w1 + w2 <= u*E[w1+w2]) on u in [0.05, 0.8]
lies in [1.6, 2.2] at N in {400, 1000, 4000}. FALSIFIER: slope <= 1.2.
Also reports: single slopes, correlation, factorization ratio
joint/(P(w1<=u)P(w2<=u)).
"""
import numpy as np, json, math, time, sys

SEED = (1111089585816317988 // 11) % (2**32)
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

def run_N(N, ndraw=80000):
    y, y1, lam = mollifier(N)
    c = conv_coeffs(N, y, lam)
    Ny = N * y
    spf = spf_sieve(Ny); ps = primes_upto(Ny)
    pidx = {int(p): i for i, p in enumerate(ps)}
    pr = primes_upto(N)
    S1 = [int(p) for p in pr if p > N ** (15 / 16)]
    S2 = [int(p) for p in pr if N ** (9 / 16) < p <= N ** (5 / 8)]
    comp = {}
    for p in S1 + S2:
        ks = np.arange(1, Ny // p + 1)
        wk = c[p * ks]; nz = wk != 0
        comp[p] = (ks[nz], wk[nz] / np.sqrt(ks[nz]))
    w1s = []; w2s = []
    B = 400
    for b in range(0, ndraw, B):
        nb = min(B, ndraw - b)
        Xp = np.exp(2j * math.pi * rng.random((nb, len(ps))))
        X = np.ones((nb, Ny + 1), dtype=complex)
        for n in range(2, Ny + 1):
            p = spf[n]
            X[:, n] = X[:, n // p] * Xp[:, pidx[int(p)]]
        def wsum(S):
            wv = np.zeros(nb)
            for p in S:
                ks, wk = comp[p]
                wv += np.abs(X[:, ks] @ wk) ** 2 / p
            return wv
        w1s.append(wsum(S1)); w2s.append(wsum(S2))
    w1 = np.concatenate(w1s); w2 = np.concatenate(w2s)
    tot = w1 + w2
    totn = tot / tot.mean()
    w1n = w1 / w1.mean(); w2n = w2 / w2.mean()
    us = np.array([0.05, 0.1, 0.2, 0.4, 0.8])
    Pj = [(totn <= u).mean() for u in us]
    P1 = [(w1n <= u).mean() for u in us]
    P2 = [(w2n <= u).mean() for u in us]
    def slope(Ps):
        m_ = [(u, q) for u, q in zip(us, Ps) if q > 3e-5]
        if len(m_) < 3: return None
        return float(np.polyfit(np.log([u for u, _ in m_]),
                                np.log([q for _, q in m_]), 1)[0])
    fac = [float(pj / (p1 * p2)) if p1 * p2 > 0 else None
           for pj, p1, p2 in zip(Pj, P1, P2)]
    out = dict(N=N, n1=len(S1), n2=len(S2),
               us=us.tolist(), Pjoint=[float(v) for v in Pj],
               P1=[float(v) for v in P1], P2=[float(v) for v in P2],
               slope_joint=slope(Pj), slope1=slope(P1), slope2=slope(P2),
               corr=float(np.corrcoef(w1, w2)[0, 1]), fac=fac)
    print(f"N={N}: |S1|={len(S1)} |S2|={len(S2)} corr(w1,w2)={out['corr']:.3f}")
    print(f"  P(joint<=u)={['%.1e' % v for v in Pj]} slope={out['slope_joint']}")
    print(f"  slopes single: w1={out['slope1']}, w2={out['slope2']}")
    print(f"  factorization joint/(P1*P2)={['%.2f' % v if v else '-' for v in fac]}")
    sys.stdout.flush()
    return out

t0 = time.time()
OUT = {'runs': [run_N(N) for N in (400, 1000, 4000)]}
OUT['runtime_s'] = time.time() - t0
with open('computations/mwm_kbdd/probe_sqrtcascade.json', 'w') as f:
    json.dump(OUT, f, indent=1)
print(f"done in {OUT['runtime_s']:.0f}s")

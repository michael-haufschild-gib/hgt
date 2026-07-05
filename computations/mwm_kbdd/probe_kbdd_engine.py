#!/usr/bin/env python3
"""(K-bdd) engine probes P4a/P4b/P5/P6 — registrations in prereg.md (they bind).

P4a/P4b: distribution of the normalized conditioned coefficients
         D_max = max_p |A_p(t)|/rms_p, D2 = second largest, p in (y, N].
P5:      pair ratio g(tau) of psi = 1_{|P|<=r} true window vs Steinhaus model.
P6:      Q(r) = meas{|P|<=r}/U true vs model.

Conventions follow mwm_mollified_dip/mollified_dip_cert.py (BV taper).
"""
import numpy as np, json, math, time, sys

SEED = 1111089585816317988 % (2**32)
rng = np.random.default_rng(SEED)
OUT = {}
t0 = time.time()

def mu_sieve(y):
    mu = np.ones(y + 1, dtype=int)
    primes = []
    is_c = np.zeros(y + 1, dtype=bool)
    for i in range(2, y + 1):
        if not is_c[i]:
            primes.append(i); mu[i] = -mu[i] if False else -1
        for p in primes:
            if i * p > y: break
            is_c[i * p] = True
            mu[i * p] = 0 if i % p == 0 else -mu[i]
            if i % p == 0: break
    mu[0] = 0
    return mu

def mollifier(N):
    y = int(round(N ** 0.5))
    y1 = max(2, int(round(y ** 0.5)))
    mu = mu_sieve(y)
    lam = mu.astype(float)
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

def eval_P_grid(c, tgrid, chunk=4000):
    m = np.nonzero(c)[0]; m = m[m >= 1]
    w = c[m] / np.sqrt(m); lm = np.log(m.astype(float))
    vals = np.empty(len(tgrid), dtype=complex)
    for i in range(0, len(tgrid), chunk):
        tc = tgrid[i: i + chunk]
        vals[i: i + chunk] = np.exp(-1j * np.outer(tc, lm)) @ w
    return vals

# ---------------- P4 ----------------
def run_P4(N, nt=20000):
    y, y1, lam = mollifier(N)
    c = conv_coeffs(N, y, lam)
    Ny = N * y
    ps = [int(p) for p in primes_upto(N) if p > y]
    T = 2 * math.pi * (N + 0.25) ** 2
    U = 2000.0
    ts = T + U * rng.random(nt)
    R = np.zeros((nt, len(ps)))
    for j, p in enumerate(ps):
        kmax = Ny // p
        ks = np.arange(1, kmax + 1)
        w = c[p * ks]
        nz = w != 0.0
        ks, w = ks[nz], w[nz]
        if len(ks) == 0: continue
        w = w / np.sqrt(p * ks)
        rms = math.sqrt(float((w ** 2).sum()))
        if rms == 0.0: continue
        lk = np.log(ks.astype(float))
        for i in range(0, nt, 4000):
            tc = ts[i: i + 4000]
            A = np.exp(-1j * np.outer(tc, lk)) @ w
            R[i: i + 4000, j] = np.abs(A) / rms
    R.sort(axis=1)
    Dmax = R[:, -1]; D2 = R[:, -2]
    eps = np.array([0.15, 0.2, 0.3, 0.4, 0.5, 0.6, 0.8])
    pa = [(Dmax < e).mean() for e in eps]
    pb = [(D2 < e).mean() for e in eps]
    def slope(ps_):
        m_ = [(e, p_) for e, p_ in zip(eps, ps_) if p_ > 0]
        if len(m_) < 3: return None
        x = np.log([e for e, _ in m_]); z = np.log([p_ for _, p_ in m_])
        return float(np.polyfit(x, z, 1)[0])
    out = dict(N=N, nprimes=len(ps), eps=eps.tolist(), P_Dmax=pa, P_D2=pb,
               slope_max=slope(pa), slope_D2=slope(pb),
               reg_a=[bool(p_ <= 2 * e ** 4 + 3*math.sqrt(max(p_,1e-9)/nt)) for e, p_ in zip(eps, pa)],
               reg_b=[bool(p_ <= 2 * e ** 2 + 3*math.sqrt(max(p_,1e-9)/nt)) for e, p_ in zip(eps, pb)])
    print(f"P4 N={N}: slope_max={out['slope_max']}, slope_D2={out['slope_D2']}")
    print(f"   P(Dmax<eps)={['%.2e' % v for v in pa]}")
    print(f"   P(D2  <eps)={['%.2e' % v for v in pb]}")
    sys.stdout.flush()
    return out

OUT['P4'] = [run_P4(N) for N in (100, 400, 1000)]

# ---------------- P5 + P6 true side ----------------
def true_side(N, U, dt, r_list):
    y, y1, lam = mollifier(N)
    c = conv_coeffs(N, y, lam)
    T = 2 * math.pi * (N + 0.25) ** 2
    tg = T + np.arange(0.0, U, dt)
    P = eval_P_grid(c, tg)
    A = np.abs(P)
    return {f"{r:g}": float((A <= r).mean()) for r in r_list}, A

R_LIST = [0.1, 0.2, 0.3, 0.5]
TAUS = [1, 2, 5, 10, 20, 50, 100]
print("true side N=400 (P5+P6)..."); sys.stdout.flush()
Q400, A400 = true_side(400, 24000.0, 0.04, R_LIST)
r5 = 0.3
psi = (A400 <= r5).astype(float)
mpsi = psi.mean()
g_true = {}
for tau in TAUS:
    k = int(round(tau / 0.04))
    g_true[tau] = float((psi[:-k] * psi[k:]).mean() / mpsi ** 2)
print("g_true:", {k: round(v, 3) for k, v in g_true.items()}); sys.stdout.flush()

print("true side N=100, N=1000 (P6)..."); sys.stdout.flush()
Q100, _ = true_side(100, 4000.0, 0.02, R_LIST)
Q1000, _ = true_side(1000, 2000.0, 0.04, R_LIST)

# ---------------- model side ----------------
def model_setup(N):
    y, y1, lam = mollifier(N)
    c = conv_coeffs(N, y, lam)
    m = np.nonzero(c)[0]; m = m[m >= 1]
    w = c[m] / np.sqrt(m); lm = np.log(m.astype(float))
    Ny = N * y
    spf = spf_sieve(Ny)
    ps = primes_upto(Ny)
    pidx = {int(p): i for i, p in enumerate(ps)}
    return m, w, lm, spf, ps, pidx, Ny

def model_X_block(B, m, spf, ps, pidx, Ny):
    Xp = np.exp(2j * math.pi * rng.random((B, len(ps))))
    X = np.ones((B, Ny + 1), dtype=complex)
    for n in range(2, Ny + 1):
        p = spf[n]
        X[:, n] = X[:, n // p] * Xp[:, pidx[int(p)]]
    return X[:, m]

def model_traj(N, ndraw, tmax, dt, r_list, taus, r5):
    m, w, lm, spf, ps, pidx, Ny = model_setup(N)
    tg = np.arange(0.0, tmax, dt)
    E = np.exp(-1j * np.outer(lm, tg))
    hits = {f"{r:g}": 0 for r in r_list}; tot = 0
    numer = {tau: 0.0 for tau in taus}; den = 0.0; npair = {tau: 0 for tau in taus}
    B = 8
    for b in range(0, ndraw, B):
        X = model_X_block(min(B, ndraw - b), m, spf, ps, pidx, Ny)
        tr = (X * w[None, :]) @ E
        Aa = np.abs(tr)
        for r in r_list: hits[f"{r:g}"] += int((Aa <= r).sum())
        tot += Aa.size
        pb_ = (Aa <= r5).astype(float)
        den += pb_.sum()
        for tau in taus:
            k = int(round(tau / dt))
            numer[tau] += float((pb_[:, :-k] * pb_[:, k:]).sum())
            npair[tau] += pb_[:, :-k].size
    q = {k_: v / tot for k_, v in hits.items()}
    mp = den / tot
    g = {tau: (numer[tau] / npair[tau]) / mp ** 2 for tau in taus}
    return q, g

print("model side N=400 trajectories..."); sys.stdout.flush()
qm400, g_model = model_traj(400, 400, 220.0, 0.04, R_LIST, TAUS, r5)
print("g_model:", {k: round(v, 3) for k, v in g_model.items()}); sys.stdout.flush()

def model_onept(N, ndraw, r_list):
    m, w, lm, spf, ps, pidx, Ny = model_setup(N)
    hits = {f"{r:g}": 0 for r in r_list}; tot = 0
    B = 400
    for b in range(0, ndraw, B):
        X = model_X_block(min(B, ndraw - b), m, spf, ps, pidx, Ny)
        vals = np.abs((X * w[None, :]).sum(1))
        for r in r_list: hits[f"{r:g}"] += int((vals <= r).sum())
        tot += len(vals)
    return {k_: v / tot for k_, v in hits.items()}

print("model one-point N=100, N=1000..."); sys.stdout.flush()
qm100 = model_onept(100, 50000, R_LIST)
qm1000 = model_onept(1000, 30000, R_LIST)

OUT['P5'] = dict(r=r5, g_true=g_true, g_model={str(k): v for k, v in g_model.items()},
                 ratio={str(t): g_true[t] / g_model[t] for t in TAUS})
OUT['P6'] = dict(true={'100': Q100, '400': Q400, '1000': Q1000},
                 model={'100': qm100, '400': qm400, '1000': qm1000})

print("\n==== ADJUDICATION ====")
for t_ in TAUS:
    rat = g_true[t_] / g_model[t_]
    print(f"P5 tau={t_}: g_true={g_true[t_]:.3f} g_model={g_model[t_]:.3f} ratio={rat:.3f} {'PASS' if abs(rat-1)<=0.10 else 'FAIL'}")
for Ntag, qt, qm in (('100', Q100, qm100), ('400', Q400, qm400), ('1000', Q1000, qm1000)):
    for r in R_LIST:
        k_ = f"{r:g}"
        if qm[k_] > 0:
            rat = qt[k_] / qm[k_]
            print(f"P6 N={Ntag} r={r}: Q_true={qt[k_]:.2e} Q_model={qm[k_]:.2e} ratio={rat:.3f} {'PASS' if abs(rat-1)<=0.15 else 'FAIL'}")

OUT['runtime_s'] = time.time() - t0
with open('computations/mwm_kbdd/probe_kbdd_engine.json', 'w') as f:
    json.dump(OUT, f, indent=1)
print(f"done in {OUT['runtime_s']:.0f}s")

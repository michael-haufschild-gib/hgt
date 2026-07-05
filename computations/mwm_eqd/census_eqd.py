#!/usr/bin/env python3
"""Doc 80 census (v2, vectorized): the (EQD) Fourier-majorant collision
framework at T = 3e12. P-EQ1..P-EQ5 pre-registered in doc 80 SS4; they bind.

Double Beurling-Selberg architecture:
  certified tail <= (1 + 1/(T*delta)) * [ model_tail(s - 1.5/U) + collision_sum(delta, U) ]
Collision sum = weighted census of coprime pairs with |log(A/B)| <= delta.
Weights are generated multiplicatively with the smooth numbers.
"""
import numpy as np, json, math
from math import log, sqrt

T = 3.0e12
OUT = {}

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

P_all = primes_upto(10**4)
B1P = P_all[P_all <= 313]
B2P = P_all[(P_all > 313) & (P_all <= 10**4)]
OUT['nB1'] = int(len(B1P)); OUT['nB2'] = int(len(B2P))
M1 = float(np.sum(1.0/np.sqrt(B1P))); M2 = float(np.sum(1.0/np.sqrt(B2P)))
OUT['M1'] = M1; OUT['M2'] = M2
OUT['sigma2_B1'] = float(np.sum(1.0/B1P))/2.0
OUT['sigma2_B2'] = float(np.sum(1.0/B2P))/2.0

def chernoff(pl, s, vmax=40.0, nv=4000):
    v = np.linspace(1e-3, vmax, nv)
    lg = -v*s + np.sum(np.log(np.i0(np.outer(1.0/np.sqrt(pl), v))), axis=0)
    return float(np.exp(lg.min()))

def total_weight(pl, u):
    x = u/(2.0*np.sqrt(pl))
    return float(np.exp(np.sum(np.log(2*np.exp(x) - 1))) - 1.0)

def graded_weight(pl, u, mmax=40):
    poly = np.zeros(mmax + 1); poly[0] = 1.0
    for p in pl:
        x = u/(2.0*sqrt(p))
        f = np.zeros(mmax + 1); f[0] = 1.0
        xk = 1.0
        for k in range(1, mmax + 1):
            xk *= x/k
            f[k] = 2.0*xk
        poly = np.convolve(poly, f)[:mmax + 1]
    return poly

def smooth_with_weights(pl, bound, u):
    """each B1P-smooth number generated exactly once; weight = prod (u/(2 sqrt p))^{e_p}/e_p!"""
    vals = np.array([1.0]); wts = np.array([1.0])
    for p in pl:
        x = u/(2.0*sqrt(p))
        acc_v = [vals]; acc_w = [wts]
        k = 0; fac = 1.0; xk = 1.0; pk = 1.0
        while True:
            k += 1; fac *= k; xk *= x; pk *= p
            new_v = vals*pk
            m = new_v <= bound
            if not m.any(): break
            acc_v.append(new_v[m]); acc_w.append(wts[m]*(xk/fac))
        vals = np.concatenate(acc_v); wts = np.concatenate(acc_w)
    o = np.argsort(vals)
    return vals[o], wts[o]

def b1_census(pl, bound, qmax, delta_rel, u):
    vals, wts = smooth_with_weights(pl, float(bound), u)
    iv = vals.astype(np.int64)
    hi = np.searchsorted(vals, vals + np.minimum(qmax, delta_rel*vals), side='right')
    counts = hi - np.arange(len(vals)) - 1
    counts = np.maximum(counts, 0)
    idx_i = np.repeat(np.arange(len(vals)), counts)
    offs = np.concatenate([np.arange(1, c + 1) for c in counts]) if counts.sum() > 0 else np.array([], dtype=int)
    idx_j = idx_i + offs
    A = iv[idx_i]; B = iv[idx_j]
    g = np.gcd(A, B)
    cop = g == 1
    A = A[cop]; B = B[cop]
    wA = wts[idx_i][cop]; wB = wts[idx_j][cop]
    om = np.log(B.astype(float)/A.astype(float))
    w = wA*wB
    avg = np.minimum(1.0, 2.0/(T*om))
    contrib = w*avg
    top = np.argsort(contrib)[::-1][:10]
    return dict(n_pairs=int(len(A)), weight_sum=float(w.sum()),
                weighted_avg_sum=float(contrib.sum()),
                min_omega=float(om.min()) if len(om) else None,
                top=[[float(f'{contrib[t]:.3e}'), int(A[t]), int(B[t])] for t in top])

def b2_census(pl, delta, u):
    logs = np.log(pl.astype(float))
    w1 = (u/2.0)/np.sqrt(pl.astype(float))
    res = {}
    # 1v1
    o = np.argsort(logs); lg = logs[o]; w1s = w1[o]
    d = np.diff(lg)
    res['1v1_min_omega'] = float(d.min())
    hi = np.searchsorted(lg, lg + delta, side='right')
    cnt = hi - np.arange(len(lg)) - 1
    idx_i = np.repeat(np.arange(len(lg)), np.maximum(cnt, 0))
    offs = np.concatenate([np.arange(1, c + 1) for c in np.maximum(cnt, 0)]) if cnt.sum() > 0 else np.array([], dtype=int)
    idx_j = idx_i + offs
    om = lg[idx_j] - lg[idx_i]
    contrib = w1s[idx_i]*w1s[idx_j]*np.minimum(1.0, 2.0/(T*om))
    res['1v1'] = dict(pairs=int(len(om)), contrib=float(contrib.sum()))
    # 2v2 products (incl squares, weight /2)
    iu = np.triu_indices(len(pl))
    plog = logs[iu[0]] + logs[iu[1]]
    pw = np.where(iu[0] == iu[1], 0.5, 1.0)*w1[iu[0]]*w1[iu[1]]
    shared_lo = pl[iu[0]]; shared_hi = pl[iu[1]]
    o2 = np.argsort(plog); plog = plog[o2]; pw = pw[o2]
    p_lo = shared_lo[o2]; p_hi = shared_hi[o2]
    dmin = np.diff(plog)
    res['2v2_min_omega_raw'] = float(dmin[dmin > 1e-14].min())
    # dyadic shells: mass_j = sum_i pw_i * (pw prefix mass in [plog_i + lo, plog_i + hi])
    cw = np.concatenate([[0.0], np.cumsum(pw)])
    tot = 0.0; shell_info = []
    for j in range(50):
        hi_o = delta*2.0**(-j); lo_o = delta*2.0**(-j - 1)
        if hi_o < 1e-14: break
        a_idx = np.searchsorted(plog, plog + lo_o, side='left')
        b_idx = np.searchsorted(plog, plog + hi_o, side='right')
        mass = float(np.sum(pw*(cw[b_idx] - cw[a_idx])))
        c = mass*min(1.0, 2.0/(T*lo_o))
        tot += c
        if mass > 0: shell_info.append([j, float(f'{mass:.3e}'), float(f'{c:.3e}')])
    res['2v2_contrib_upper'] = float(tot)
    res['2v2_shells_head'] = shell_info[:6]
    return res

def christoffel_tail(moms, a):
    n = (len(moms) - 1)//2
    H = np.array([[moms[i + j] for j in range(n + 1)] for i in range(n + 1)])
    L = np.linalg.cholesky(H)
    Linv = np.linalg.inv(L)
    xs = np.array([(-a)**k for k in range(n + 1)])
    pv = Linv @ xs
    return 1.0/float(np.sum(pv**2))

def gauss_moments(sig2, n, m4ratio=1.0):
    m = [1.0, 0.0, sig2, 0.0]
    if n >= 2: m.append(3.0*sig2**2*m4ratio)
    return m[:2*n + 1]

def block_ladder(pl, n):
    kcos = {2: 0.5, 4: -0.375, 6: 1.25, 8: -1155/128, 10: 3591/32}
    s = {j: float(np.sum(pl.astype(float)**(-j))) for j in (1, 2, 3, 4, 5)}
    kap = {2*j: kcos[2*j]*s[j] for j in (1, 2, 3, 4, 5)}
    moms = [1.0, 0.0]
    for r in range(2, 2*n + 1):
        m = 0.0
        for jj in range(2, r + 1):
            kj = kap.get(jj, 0.0)
            if kj != 0.0:
                m += math.comb(r - 1, jj - 1)*kj*moms[r - jj]
        moms.append(m)
    return moms

# ============ RUN ============
OUT['model_chernoff_B1'] = {str(a): chernoff(B1P, a) for a in (3.1, 3.6, 4.1, 4.6, 5.1, 6.1)}
OUT['model_chernoff_B2'] = {str(a): chernoff(B2P, a) for a in (1.0, 1.25, 1.5, 2.0)}

u1 = 3.0
OUT['W1_total_u3'] = total_weight(B1P, u1)
Wm = graded_weight(B1P, u1, 40)
OUT['W1_graded_head'] = [float(f'{x:.4e}') for x in Wm[:12]]
OUT['flat_far_bound_delta1e-2'] = 2*OUT['W1_total_u3']/(T*1e-2)

OUT['b1_census_u3'] = b1_census(B1P, 3_000_000, 500.0, 1e-2, u1)
u2 = 1.8
OUT['b2_census_u1p8'] = b2_census(B2P, 1e-2, u2)

# ---- assembly at A = 6.1: B1 Fourier + B2 deg-6 + B3 deg-4 + residual deg-4 ----
delta1 = 100.0/T
OUT['delta1'] = delta1
ladB2 = block_ladder(B2P, 3)
OUT['ladderB2'] = [float(f'{x:.5e}') for x in ladB2]
ladR = [1.0, 0.0, 0.23, 0.0, 2.0*3*0.23**2]

def b1_fourier_tail(s):
    return chernoff(B1P, max(0.3, s - 1.5/u1))*(1 + 1.0/(T*delta1))
def b2_tail(s):  return christoffel_tail(ladB2, s)
def b3_tail(s):  return christoffel_tail(gauss_moments(0.189, 2), s)
def r_tail(s):   return christoffel_tail(ladR, max(0.05, s - 0.36))

best = (9e9, None)
for sA in np.arange(2.0, 5.4, 0.05):
    tA = b1_fourier_tail(sA)
    if tA > 0.02: continue
    for sB in np.arange(0.4, 6.1 - sA - 0.4, 0.05):
        tB = b2_tail(sB)
        rem = 6.1 - sA - sB
        if rem <= 0.3: continue
        for sC in np.arange(0.2, rem - 0.1, 0.05):
            sR = rem - sC
            tot = tA + tB + b3_tail(sC) + r_tail(sR)
            if tot < best[0]:
                best = (tot, (round(float(sA), 2), round(float(sB), 2),
                              round(float(sC), 2), round(float(sR), 2)))
OUT['assembled_stack_A6.1'] = dict(total=float(best[0]), alloc=best[1])

# reference: doc74-style all-Christoffel 4-block (B1 deg-10)
ladB1 = block_ladder(B1P, 5)
def b1_c10(s): return christoffel_tail(ladB1, s)
best2 = (9e9, None)
for sA in np.arange(2.0, 5.4, 0.05):
    tA = b1_c10(sA)
    for sB in np.arange(0.4, 6.1 - sA - 0.4, 0.05):
        tB = b2_tail(sB)
        rem = 6.1 - sA - sB
        if rem <= 0.3: continue
        for sC in np.arange(0.2, rem - 0.1, 0.05):
            sR = rem - sC
            tot = tA + tB + b3_tail(sC) + r_tail(sR)
            if tot < best2[0]:
                best2 = (tot, (round(float(sA), 2), round(float(sB), 2),
                               round(float(sC), 2), round(float(sR), 2)))
OUT['reference_all_christoffel'] = dict(total=float(best2[0]), alloc=best2[1])

print(json.dumps(OUT, indent=1, default=str))

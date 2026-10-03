# S44: non-perturbative "zero completion" search for real-rooted F = a*zeta^2*B_N + E, E in visible W2(N),
# started far from the arithmetic point.  Iterate LPs: keep existing sign pattern (sampled), flip sign at the
# K deepest |Z_F| local minima between sign changes (missing zeros), trust region on the step.
# Report the best real-rootedness height T_RR = largest T' <= T with sign changes on [0,T'] = full count.
import numpy as np, mpmath as mp, json, sys, time
from scipy.optimize import linprog
from scipy.linalg import svd
from afe import *
from twinlp import siegelz_list
from multiprocessing import Pool
d = 2
def build(T, lq, margin=60.0, mult=4.0, thr=1e-8):
    Tc = T + margin; nt = np.exp(lq/2)*(Tc/(2*np.pi)); N = int(np.ceil(mult*nt)) + 5
    n = np.arange(1, N + 1, dtype=float); td = np.arange(0.05, Tc, 0.08)
    D = defect_rows(td, n, d, lq, sigma0=3.0, c1=0.5, c2=2.5)
    A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
    U, s, Vt = svd(A, full_matrices=True); s = s/s[0]; s = np.concatenate([s, np.zeros(N - len(s))])
    return n, Vt[s < thr].T
def Theta(t, lq): return d*float(mp.siegeltheta(t)) + 0.5*t*lq
def count_ok(tg, Z, lq, pole):
    sc = np.cumsum(np.concatenate([[0], (np.sign(Z[1:]) != np.sign(Z[:-1])).astype(int)]))
    best = 0.0
    for i in range(0, len(tg), 50):
        need = Theta(tg[i], lq)/np.pi + pole
        if sc[i] >= np.floor(need) - 0: best = tg[i]
        elif tg[i] > 15: break
    return best, int(sc[-1])
def run(Ncond, T, a, seed, pool, iters=40, K=4):
    rng = np.random.default_rng(seed); lq = np.log(Ncond)
    n, B = build(T, lq); tg = np.arange(0.3, T, 0.005)
    Zz = np.array(sum(pool.map(siegelz_list, np.array_split(tg, 32)), []))
    Z0 = a*2*np.cos(tg*lq/2)*Zz**2
    R = Zrows(tg, n, d, lq, a=0.02) @ B
    u, sv, vt = np.linalg.svd(R, full_matrices=False); keep = sv > 1e-6*sv[0]; P = vt[keep].T; R = R @ P; k = P.shape[1]
    scale = np.sqrt(np.mean(Z0**2)) if a else 1.0
    c = rng.normal(size=k); c *= 3*scale/np.sqrt(np.mean((R @ c)**2))       # far from the arithmetic point
    pole = 2 if a else 0
    hist = []
    for it in range(iters):
        ZF = Z0 + R @ c
        tr, sc = count_ok(tg, ZF, lq, pole); hist.append(round(float(tr), 1))
        s = np.sign(ZF); chg = np.where(s[1:] != s[:-1])[0]
        # candidate missing zeros: local minima of |ZF| strictly between sign changes, ranked by |ZF|/local scale
        absz = np.abs(ZF); lm = np.where((absz[1:-1] < absz[:-2]) & (absz[1:-1] < absz[2:]))[0] + 1
        lm = [i for i in lm if absz[i] > 0 and not np.any(np.abs(chg - i) < 20)]
        if not lm: break
        loc = np.array([absz[max(0, i-200):i+200].max() for i in lm]); score = absz[lm]/loc
        targ = [lm[j] for j in np.argsort(score)[:K]]
        keep_idx = np.arange(0, len(tg), 20); keep_idx = np.array([i for i in keep_idx if all(abs(i - t) > 40 for t in targ)])
        rows = np.vstack([s[keep_idx][:, None]*R[keep_idx], (-s[targ])[:, None]*R[targ]])
        rhs = np.concatenate([s[keep_idx]*ZF[keep_idx], -s[targ]*ZF[targ]])
        w = np.concatenate([np.abs(ZF[keep_idx]), 0.2*loc[np.argsort(score)[:K]]]) + 1e-12
        # step dc: rows dc + rhs >= m w, |dc| <= r ; maximize m
        r = 2.0*np.max(np.abs(c)) + 1.0
        Aub = np.hstack([-rows, w[:, None]]); bub = rhs
        res = linprog(np.concatenate([np.zeros(k), [-1.0]]), A_ub=Aub, b_ub=bub, bounds=[(-r, r)]*k + [(None, 1.0)], method="highs")
        if res.status != 0 or res.x[-1] <= 0: break
        c = c + res.x[:k]
    ZF = Z0 + R @ c; tr, sc = count_ok(tg, ZF, lq, pole)
    rec = dict(N=Ncond, T=T, a=a, seed=seed, kvis=k, T_RR=round(float(tr), 1), sc=sc, need=round(Theta(T, lq)/np.pi + pole, 1), iters=len(hist), hist=hist[:12])
    print(json.dumps(rec), flush=True); return rec
if __name__ == "__main__":
    Ns = [float(x) for x in sys.argv[1].split(",")]; T = float(sys.argv[2]); seeds = int(sys.argv[3])
    with Pool(8) as pool:
        for Ncond in Ns:
            for a in (1.0, 0.0):
                for sd in range(seeds): run(Ncond, T, a, sd, pool)

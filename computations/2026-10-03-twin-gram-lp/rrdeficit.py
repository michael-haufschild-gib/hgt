# S3: minimal real-zero deficit of F = s0*zeta^d + E (E in approximate W_d) on [0,T].
# L1-LP over Gram points (allow violations, minimize total slack), then count sign changes of Z_F
# on a fine grid and compare with the expected zero count d*theta(T)/pi + d (pole case) or d*theta/pi (entire).
import numpy as np, mpmath as mp, json, sys, time
from scipy.optimize import linprog
from scipy.linalg import svd
from afe import *
from twinlp import gram_points, siegelz_list
from multiprocessing import Pool

def build(d, T, margin=60.0, mult=4.0, thr=1e-8):
    Tc = T + margin; nt = (Tc/(2*np.pi))**(d/2); N = int(np.ceil(mult*nt)) + 5
    n = np.arange(1, N+1, dtype=float)
    td = np.arange(0.05, Tc, 0.08)
    D = defect_rows(td, n, d, 0.0, sigma0=3.0, c1=0.5, c2=2.5)
    A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
    U, s, Vt = svd(A, full_matrices=True); s = s/s[0]
    s = np.concatenate([s, np.zeros(N - len(s))])
    return n, Vt[s < thr].T

def run(d, T, s0, phase, pool, CB=1e3):
    t0 = time.time()
    n, B = build(d, T); k = B.shape[1]
    gp = gram_points(d, T)
    js = np.array([j for j, g in gp], float); gs = np.array([g for j, g in gp])
    if phase != 0.0:   # shifted Gram grid: d*theta(t) = (j+phase)*pi
        gs2 = []
        for j, g in gp:
            target = (j + phase)*np.pi/d; x = g
            for _ in range(30): x -= (float(mp.siegeltheta(x)) - target)/(0.5*np.log(x/(2*np.pi)))
            gs2.append(x)
        gs = np.array(gs2)
    tg = np.arange(0.5, T, 0.01)
    allt = np.concatenate([gs, tg])
    Zz = np.array(sum(pool.map(siegelz_list, np.array_split(allt, 32)), []))
    Zd = s0*Zz**d
    R = Zrows(allt, n, d, 0.0, a=0.02) @ B
    G = len(gs); sg = (-1.0)**js
    scale = np.median(np.abs(R[:G]), axis=0) + 1e-300
    # variables: c (k), slack (G) >= 0 ; constraint sg*(Zd + R c) + slack >= 1 ; min sum slack
    # restrict to certified visible directions: right singular vectors of R on the fine grid with sv > 1e-6*max,
    # and cross-check with a second AFE weight
    Rf = R[G:]
    u, sv, vt = np.linalg.svd(Rf, full_matrices=False)
    keep = sv > 1e-6*sv[0]
    P = vt[keep].T                       # k x m
    R = R @ P; B = B @ P; k = P.shape[1]
    R2 = Zrows(allt[G::25], n, d, 0.0, a=0.05) @ B
    werr = float(np.max(np.abs(R2 - R[G::25])))
    # coefficient bound |e_n| <= CB * d_d(n)
    N = len(n); dd = np.ones(N)
    for _ in range(d-1):
        nd = np.zeros(N)
        for i in range(1, N+1): nd[i-1::i] += dd[i-1]
        dd = nd
    Rg = R[:G]
    cobj = np.concatenate([np.zeros(k), np.ones(G)])
    A1 = np.hstack([-(sg[:, None]*Rg), -np.eye(G)]); b1 = sg*Zd[:G] - 1.0
    A2 = np.hstack([B, np.zeros((N, G))]); A3 = np.hstack([-B, np.zeros((N, G))])
    Aub = np.vstack([A1, A2, A3]); bub = np.concatenate([b1, CB*dd, CB*dd])
    res = linprog(cobj, A_ub=Aub, b_ub=bub, bounds=[(None, None)]*k + [(0, None)]*G, method="highs")
    c = res.x[:k]; sl = res.x[k:]
    ZF = Zd[G:] + R[G:] @ c
    sc = int(np.sum(np.sign(ZF[1:]) != np.sign(ZF[:-1])))
    expected = d*float(mp.siegeltheta(T))/np.pi + (d if s0 != 0 else 0)
    base = int(np.sum(np.sign(Zd[G:][1:]) != np.sign(Zd[G:][:-1]))) if s0 != 0 else None
    rec = dict(d=d, T=T, zeta_part=s0, phase=phase, k=k, gram=G, violated=int(np.sum(sl > 1e-6)),
               slack=round(float(np.sum(sl)), 3), signchanges=sc, expected=round(expected, 2),
               zeta_d_signchanges=base, coef_inf=float("%.3g" % np.max(np.abs(B @ c))), kvis=k, werr=float("%.1e" % werr), CB=CB, time=round(time.time()-t0, 1))
    print(json.dumps(rec), flush=True)
    return rec

if __name__ == "__main__":
    d = int(sys.argv[1]); Ts = [float(x) for x in sys.argv[2].split(",")]
    with Pool(8) as pool:
        for T in Ts:
            for s0 in (1.0, 0.0):
                for CB in (1e1, 1e3):
                    run(d, T, s0, 0.0, pool, CB)

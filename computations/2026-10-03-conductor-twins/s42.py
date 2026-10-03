# S42: local real-rooted twins of zeta^3 at conductor N.  Base F0 = zeta^3 * (1 + N^{1/2-s}) (in V3(N), eps=+1),
# Z_F0(t) = 2 cos(t log N / 2) Z_zeta(t)^3.  Add E in certified visible W3(N) (entire part, conductor N),
# L1-LP on Gram points of Theta = 3 theta + (t/2) log N (Gram's law for F), coefficient bound |e_n| <= CB d3(n).
# Count sign changes of Z_F on a fine grid vs base and vs the full zero count Theta(T)/pi + 3.
import numpy as np, mpmath as mp, json, sys, time
from scipy.optimize import linprog
from scipy.linalg import svd
from afe import *
from twinlp import siegelz_list
from multiprocessing import Pool
d = 3

def Theta(t, lq): return d*float(mp.siegeltheta(t)) + 0.5*t*lq
def gram(T, lq):
    out = []; t0 = 10.0; j = int(np.ceil(Theta(t0, lq)/np.pi)); x = t0
    while True:
        target = j*np.pi
        for _ in range(60):
            dth = 1.5*np.log(max(x, 7.0)/(2*np.pi)) + 0.5*lq
            x = max(x - (Theta(x, lq) - target)/max(dth, 0.05), t0)
        if x > T or len(out) > 100000: break
        if abs(Theta(x, lq) - target) < 1e-6: out.append((j, x))
        j += 1; x += 0.2
    return out

def build(T, lq, margin=60.0, mult=4.0, thr=1e-8):
    Tc = T + margin; nt = np.exp(lq/2)*(Tc/(2*np.pi))**(d/2); N = int(np.ceil(mult*nt)) + 5
    n = np.arange(1, N + 1, dtype=float)
    td = np.arange(0.05, Tc, 0.08)
    D = defect_rows(td, n, d, lq, sigma0=3.0, c1=0.5, c2=2.5)
    A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
    U, s, Vt = svd(A, full_matrices=True); s = s/s[0]
    s = np.concatenate([s, np.zeros(N - len(s))])
    return n, Vt[s < thr].T

def run(Ncond, T, s0, CB, pool):
    t0 = time.time(); lq = np.log(Ncond)
    n, B = build(T, lq); gp = gram(T, lq)
    js = np.array([j for j, g in gp], float); gs = np.array([g for j, g in gp])
    tg = np.arange(0.5, T, 0.01); allt = np.concatenate([gs, tg])
    Zz = np.array(sum(pool.map(siegelz_list, np.array_split(allt, 32)), []))
    Z0 = s0*2*np.cos(allt*lq/2)*Zz**3
    R = Zrows(allt, n, d, lq, a=0.02) @ B
    G = len(gs); sg = (-1.0)**js
    Rf = R[G:]; u, sv, vt = np.linalg.svd(Rf, full_matrices=False); keep = sv > 1e-6*sv[0]
    P = vt[keep].T; R = R @ P; B = B @ P; k = P.shape[1]
    R2 = Zrows(allt[G::25], n, d, lq, a=0.05) @ B; werr = float(np.max(np.abs(R2 - R[G::25]))) if k else 0.0
    Nn = len(n); dd = np.ones(Nn)
    for _ in range(d - 1):
        nd = np.zeros(Nn)
        for i in range(1, Nn + 1): nd[i-1::i] += dd[i-1]
        dd = nd
    Rg = R[:G]
    cobj = np.concatenate([np.zeros(k), np.ones(G)])
    A1 = np.hstack([-(sg[:, None]*Rg), -np.eye(G)]); b1 = sg*Z0[:G] - 1.0
    A2 = np.hstack([B, np.zeros((Nn, G))]); A3 = np.hstack([-B, np.zeros((Nn, G))])
    res = linprog(cobj, A_ub=np.vstack([A1, A2, A3]), b_ub=np.concatenate([b1, CB*dd, CB*dd]),
                  bounds=[(None, None)]*k + [(0, None)]*G, method="highs")
    c = res.x[:k] if res.status == 0 else np.zeros(k); sl = res.x[k:] if res.status == 0 else np.ones(G)
    ZF = Z0[G:] + R[G:] @ c
    sc = int(np.sum(np.sign(ZF[1:]) != np.sign(ZF[:-1])))
    base = int(np.sum(np.sign(Z0[G:][1:]) != np.sign(Z0[G:][:-1]))) if s0 else None
    expected = Theta(T, lq)/np.pi + (3 if s0 else 0)
    rec = dict(N=Ncond, T=T, base_part=s0, CB=CB, kvis=k, gram=G, violated=int(np.sum(sl > 1e-6)), slack=round(float(np.sum(sl)), 2),
               signchanges=sc, base_signchanges=base, expected=round(expected, 1), coef_inf=float("%.3g" % (np.max(np.abs(B @ c)) if k else 0)),
               werr=float("%.1e" % werr), status=int(res.status), time=round(time.time() - t0, 1))
    print(json.dumps(rec), flush=True); return rec

if __name__ == "__main__":
    Ns = [float(x) for x in sys.argv[1].split(",")]; Ts = [float(x) for x in sys.argv[2].split(",")]
    with Pool(8) as pool:
        for Ncond in Ns:
            for T in Ts:
                for s0, CB in ((1.0, 1e1), (1.0, 1e3), (0.0, 1e3)):
                    run(Ncond, T, s0, CB, pool)

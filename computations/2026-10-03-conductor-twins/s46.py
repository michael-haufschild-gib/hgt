# S46: local trigonal handles.  F = zeta^3*B_N + E, E in visible W3(N).  At every zeta-zero gamma the base
# Z_F0 = 2cos(t log N/2) Z^3 has a triple zero (one sign change).  Require three real zeros in
# [gamma-1.5eta, gamma+1.5eta]: signs s, -s, s, -s at gamma -1.5eta, -0.5eta, +0.5eta, +1.5eta (s = base sign left);
# keep the base sign pattern elsewhere.  Maximize margin; count per-zero splits (3 sign changes in the window).
import numpy as np, mpmath as mp, json, sys, time
from scipy.optimize import linprog
from scipy.linalg import svd
from afe import *
from twinlp import siegelz_list
from multiprocessing import Pool
d = 3
def build(T, lq, margin=60.0, mult=4.0, thr=1e-8):
    Tc = T + margin; nt = np.exp(lq/2)*(Tc/(2*np.pi))**(d/2); N = int(np.ceil(mult*nt)) + 5
    n = np.arange(1, N + 1, dtype=float); td = np.arange(0.05, Tc, 0.08)
    D = defect_rows(td, n, d, lq, sigma0=3.0, c1=0.5, c2=2.5)
    A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
    U, s, Vt = svd(A, full_matrices=True); s = s/s[0]; s = np.concatenate([s, np.zeros(N - len(s))])
    return n, Vt[s < thr].T
def run(Ncond, T, eta, CB, pool, zeros):
    t0 = time.time(); lq = np.log(Ncond)
    n, B = build(T, lq); dt = 0.005; tg = np.arange(0.3, T, dt)
    Zz = np.array(sum(pool.map(siegelz_list, np.array_split(tg, 32)), []))
    Z0 = 2*np.cos(tg*lq/2)*Zz**3
    R = Zrows(tg, n, d, lq, a=0.02) @ B
    u, sv, vt = np.linalg.svd(R, full_matrices=False); keep = sv > 1e-6*sv[0]; P = vt[keep].T; R = R @ P; B = B @ P; k = P.shape[1]
    lat = (2*np.arange(0, 5000) + 1)*np.pi/lq if lq > 0 else np.array([]); lat = lat[lat < T]
    zs = [z for z in zeros if 1.6*eta < z < T - 1.6*eta and (len(lat) == 0 or np.min(np.abs(lat - z)) > 2*eta)]
    ix = lambda x: int(round((x - 0.3)/dt))
    mask = np.ones(len(tg), bool)
    for z in zs: mask &= np.abs(tg - z) > 2*eta
    for z in lat: mask &= np.abs(tg - z) > 0.05
    sel = np.where(mask)[0][::10]
    rows, rhs, wts = [], [], []
    for i in sel: rows.append(np.sign(Z0[i])*R[i]); rhs.append(np.sign(Z0[i])*Z0[i]); wts.append(abs(Z0[i]))
    for z in zs:
        sL = np.sign(Z0[ix(z - 1.5*eta)]); scale = max(abs(Z0[ix(z - 1.5*eta)]), abs(Z0[ix(z + 1.5*eta)]))
        for off, sg in ((-1.5, sL), (-0.5, -sL), (0.5, sL), (1.5, -sL)):
            i = ix(z + off*eta); rows.append(sg*R[i]); rhs.append(sg*Z0[i]); wts.append(0.3*scale)
    rows, rhs, wts = np.array(rows), np.array(rhs), np.array(wts) + 1e-15
    Nn = len(n); dd = np.ones(Nn)
    for _ in range(d - 1):
        nd = np.zeros(Nn)
        for i in range(1, Nn + 1): nd[i-1::i] += dd[i-1]
        dd = nd
    Aub = np.vstack([np.hstack([-rows, wts[:, None]]), np.hstack([B, np.zeros((Nn, 1))]), np.hstack([-B, np.zeros((Nn, 1))])])
    res = linprog(np.concatenate([np.zeros(k), [-1.0]]), A_ub=Aub, b_ub=np.concatenate([rhs, CB*dd, CB*dd]),
                  bounds=[(None, None)]*k + [(None, 1.0)], method="highs")
    m = float(res.x[-1]) if res.status == 0 else None; c = res.x[:k] if res.status == 0 else np.zeros(k)
    ZF = Z0 + R @ c
    split = 0
    for z in zs:
        w = np.abs(tg - z) < 1.6*eta; zz = ZF[w]
        if int(np.sum(np.sign(zz[1:]) != np.sign(zz[:-1]))) >= 3: split += 1
    rec = dict(N=Ncond, T=T, eta=eta, CB=CB, kvis=k, zeros=len(zs), split=split, margin=m, status=int(res.status),
               coef=float("%.3g" % (np.max(np.abs(B @ c)) if k else 0)), pred_T3=round(2*np.pi*Ncond, 1), time=round(time.time() - t0, 1))
    print(json.dumps(rec), flush=True); return rec
if __name__ == "__main__":
    Ns = [float(x) for x in sys.argv[1].split(",")]; Ts = [float(x) for x in sys.argv[2].split(",")]
    eta = float(sys.argv[3]) if len(sys.argv) > 3 else 0.2
    mp.mp.dps = 20; zeros = [float(mp.zetazero(j).imag) for j in range(1, 80)]
    with Pool(8) as pool:
        for Ncond in Ns:
            for T in Ts:
                run(Ncond, T, eta, 1e3, pool, zeros)

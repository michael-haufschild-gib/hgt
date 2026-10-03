# S43: real-rooted degree-2 Dirichlet series at conductor N (Hecke group of the 2nd kind for N>4)?
# Base F0 = zeta^2 * B_N, B_N = 1 + N^{1/2-s}:  Z_F0(t) = 2cos(t log N/2) Z_zeta(t)^2 (double zeros at zeta zeros).
# F = F0 + G, G in certified visible W2(N) (entire part).  Real-rootedness up to T requires each double zero to
# split into two real zeros (sign(Z_F(gamma)) = -sign(c_gamma)) and every other sign change kept.
# LP: maximize margin m s.t. s_i * Z_F(t_i) >= m * w_i on a sign-pattern grid; |g_n| <= CB d(n).
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

def run(Ncond, T, CB, pool, zeros):
    t0 = time.time(); lq = np.log(Ncond)
    n, B = build(T, lq)
    tg = np.arange(0.3, T, 0.005)
    Zz = np.array(sum(pool.map(siegelz_list, np.array_split(tg, 32)), []))
    Z0 = 2*np.cos(tg*lq/2)*Zz**2
    R = Zrows(tg, n, d, lq, a=0.02) @ B
    u, sv, vt = np.linalg.svd(R, full_matrices=False); keep = sv > 1e-6*sv[0]
    P = vt[keep].T; R = R @ P; B = B @ P; k = P.shape[1]
    # sign pattern: base sign everywhere except within +-eta of each zeta zero, where the double zero must split:
    # require sign(Z_F(gamma)) = -sign(c_gamma)  (c_gamma = sign of Z0 just off gamma)
    zs = [z for z in zeros if z < T - 0.5]
    idx_g = [int(np.argmin(np.abs(tg - z))) for z in zs]
    eta = 0.25
    mask = np.ones(len(tg), bool)
    for z in zs: mask &= np.abs(tg - z) > eta
    # also exclude neighbourhoods of the lattice zeros of B_N (simple zeros, sign flips there)
    lat = (2*np.arange(0, 1000) + 1)*np.pi/lq; lat = lat[lat < T]
    for z in lat: mask &= np.abs(tg - z) > 0.05
    sel = np.where(mask)[0][::10]
    s_base = np.sign(Z0[sel]); w_base = np.abs(Z0[sel])
    s_g = np.array([-np.sign(np.cos(z*lq/2)) for z in zs])
    w_g = np.array([np.abs(Z0[min(i + int(eta/0.005), len(tg) - 1)]) for i in idx_g])
    rows = np.vstack([s_base[:, None]*R[sel], s_g[:, None]*R[idx_g]])
    rhs0 = np.concatenate([s_base*Z0[sel], s_g*Z0[idx_g]])
    wts = np.concatenate([w_base, w_g]) + 1e-12
    # variables c (k), m ; constraint rows c + rhs0 >= m*wts  ->  -rows c + m*wts <= rhs0
    Nn = len(n); dd = np.ones(Nn); nd = np.zeros(Nn)
    for i in range(1, Nn + 1): nd[i-1::i] += 1
    dd = nd
    Aub = np.vstack([np.hstack([-rows, wts[:, None]]), np.hstack([B, np.zeros((Nn, 1))]), np.hstack([-B, np.zeros((Nn, 1))])])
    bub = np.concatenate([rhs0, CB*dd, CB*dd])
    res = linprog(np.concatenate([np.zeros(k), [-1.0]]), A_ub=Aub, b_ub=bub, bounds=[(None, None)]*k + [(None, 1.0)], method="highs")
    m = float(res.x[-1]) if res.status == 0 else None
    c = res.x[:k] if res.status == 0 else np.zeros(k)
    ZF = Z0 + R @ c
    sc = int(np.sum(np.sign(ZF[1:]) != np.sign(ZF[:-1]))); sc0 = int(np.sum(np.sign(Z0[1:]) != np.sign(Z0[:-1])))
    expected = sc0 + 2*len(zs)        # each double zero must become two simple real zeros
    loc = []
    for z in zs:
        w = np.abs(tg - z) < 0.3
        zz = ZF[w]; z0 = Z0[w]
        loc.append((int(np.sum(np.sign(zz[1:]) != np.sign(zz[:-1]))), int(np.sum(np.sign(z0[1:]) != np.sign(z0[:-1])))))
    rec = dict(N=Ncond, T=T, CB=CB, kvis=k, nzeros=len(zs), margin=m, signchanges=sc, base_signchanges=sc0,
               needed=expected, local=loc, coef_inf=float("%.3g" % (np.max(np.abs(B @ c)) if k else 0)), status=int(res.status), time=round(time.time() - t0, 1))
    print(json.dumps(rec), flush=True); return rec

if __name__ == "__main__":
    Ns = [float(x) for x in sys.argv[1].split(",")]; Ts = [float(x) for x in sys.argv[2].split(",")]
    mp.mp.dps = 20; zeros = [float(mp.zetazero(k).imag) for k in range(1, 60)]
    with Pool(8) as pool:
        for Ncond in Ns:
            for T in Ts:
                for CB in (1e1, 1e3):
                    run(Ncond, T, CB, pool, zeros)

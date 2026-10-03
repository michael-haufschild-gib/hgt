# Gram-law twin LP:  F = zeta^d + E, E in approximate W_d (Gamma_R^d, q=1, entire part).
# Gram's law in degree d:  (-1)^j Z_F(g_j) > 0 at d*theta(g_j) = j*pi.  Z_{zeta^d} = Z^d.
import numpy as np, mpmath as mp, time, sys, json
from scipy.optimize import linprog
from scipy.linalg import svd, qr
from afe import *
from multiprocessing import Pool

def siegelz_list(ts):
    mp.mp.dps = 20
    return [float(mp.siegelz(t)) for t in ts]

def gram_points(d, T):
    # solve theta(g) = j*pi/d for g in (8, T]
    out = []
    j = int(np.ceil(d*float(mp.siegeltheta(8.0))/np.pi))
    while True:
        target = j*np.pi/d
        g = 2*np.pi*np.exp(1 + float(mp.lambertw((target + np.pi/8)/(np.pi*float(mp.e))).real))  # rough
        g = float(g)
        for _ in range(30):
            g -= (float(mp.siegeltheta(g)) - target)/(0.5*np.log(g/(2*np.pi)))
        if g > T: break
        out.append((j, g)); j += 1
    return out

def run(d, T, margin=60.0, mult=4.0, thr=1e-9, delta=0.05, a=0.02, wmode="d3", pool=None):
    t0 = time.time()
    Tc = T + margin
    nt = (Tc/(2*np.pi))**(d/2)
    N = int(np.ceil(mult*nt)) + 5
    n = np.arange(1, N+1, dtype=float)
    td = np.arange(0.05, Tc, 0.08)
    D = defect_rows(td, n, d, 0.0, sigma0=3.0, c1=0.5, c2=2.5, a=a)
    A = np.vstack([D.real, D.imag]); A /= np.linalg.norm(A, axis=1, keepdims=True)
    U, s, Vt = svd(A, full_matrices=True)
    s = s/s[0]
    r = int(np.sum(s >= thr))
    B = Vt[r:].T                       # N x k null basis
    k = B.shape[1]
    # visible rank on [0,T]
    tg = np.arange(0.2, T, 0.05)
    R = Zrows(tg, n, d, 0.0, a=a)
    RB = R @ B
    sv = np.linalg.svd(RB, compute_uv=False)
    vis = {th: int(np.sum(sv/sv[0] > th)) if k else 0 for th in (1e-3, 1e-6, 1e-9)}
    # check AFE weight independence on null space: compare a and 2.5a
    R2 = Zrows(tg[::10], n, d, 0.0, a=2.5*a)
    werr = float(np.max(np.abs(R2 @ B - R[::10] @ B))) if k else 0.0
    # Gram LP
    gp = gram_points(d, T)
    js = np.array([j for j, g in gp]); gs = np.array([g for j, g in gp])
    zz = np.array(pool.map(siegelz_list, np.array_split(gs, 16)) if pool else [siegelz_list(gs)], dtype=object)
    Z = np.concatenate([np.array(x) for x in zz])
    Zd = Z**d
    sg = (-1.0)**js
    base_ok = int(np.sum(sg*Zd > 0))
    Rg = Zrows(gs, n, d, 0.0, a=a) @ B          # G x k
    if wmode == "d3":
        # divisor function d_d(n)
        dd = np.ones(N)
        for _ in range(d-1):
            nd = np.zeros(N)
            for i in range(1, N+1): nd[i-1::i] += dd[i-1]
            dd = nd
        w = dd
    else:
        w = np.ones(N)
    G = len(gs)
    # variables x = (c[0..k-1], M);  minimize M
    # -sg*(Rg c) <= sg*Zd - delta ;  B c - M w <= 0 ; -B c - M w <= 0
    cobj = np.zeros(k+1); cobj[-1] = 1.0
    A1 = np.hstack([-(sg[:, None]*Rg), np.zeros((G, 1))]); b1 = sg*Zd - delta
    A2 = np.hstack([B, -w[:, None]]); A3 = np.hstack([-B, -w[:, None]])
    Aub = np.vstack([A1, A2, A3]); bub = np.concatenate([b1, np.zeros(2*N)])
    res = linprog(cobj, A_ub=Aub, b_ub=bub, bounds=[(None, None)]*k + [(0, None)], method="highs")
    rec = dict(d=d, T=T, Tc=Tc, N=N, k=k, visible=vis, weight_err=werr, gram=G,
               gram_ok_zeta=base_ok, status=int(res.status), msg=res.message[:60])
    if res.status == 0:
        c = res.x[:k]; e = B @ c
        rec["M"] = float(res.x[-1])
        # sign changes of Z_F on fine grid
        zf_fine = np.array(sum(pool.map(siegelz_list, np.array_split(tg, 16)), [])) if pool else np.array(siegelz_list(tg))
        ZF = zf_fine**d + R @ e
        rec["signchanges"] = int(np.sum(np.sign(ZF[1:]) != np.sign(ZF[:-1])))
        rec["expected_N(T)"] = float(d*mp.siegeltheta(T)/np.pi + d)
        rec["e_small_n"] = [round(float(x), 4) for x in e[:12]]
        rec["argmax_n"] = int(np.argmax(np.abs(e)/w)) + 1
        np.save("sol_d%d_T%d.npy" % (d, int(T)), e)
    rec["time"] = round(time.time() - t0, 1)
    print(json.dumps(rec), flush=True)
    return rec

if __name__ == "__main__":
    d = int(sys.argv[1]); Ts = [float(x) for x in sys.argv[2].split(",")]
    wmode = sys.argv[3] if len(sys.argv) > 3 else "d3"
    with Pool(8) as pool:
        out = [run(d, T, wmode=wmode, pool=pool) for T in Ts]
    json.dump(out, open("twinlp_d%d_%s.json" % (d, wmode), "a"))

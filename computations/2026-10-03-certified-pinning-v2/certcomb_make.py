# Certificates for the combined (P=4 cubic, P=8) Weil LMIs at support L: for each n0 in 2..N and sign, run the
# high-precision log-barrier on the block-diagonal LMI, take the central-path duals X_b = M_b^{-1}/t (whitened,
# rescaled coordinates), map to spline coordinates Xs_b = Ci_b^T W_b X_b W_b^T Ci_b, split into rank-1 parts (mpmath
# eigsy), and write weights + vectors as 70-digit strings.  Any PSD X_b gives a valid inequality; quality is checked
# rigorously by certcomb_verify.py.
import os, sys, json, time, importlib
import mpmath as mp
from multiprocessing import Pool
from flint import arb_mat, arb, ctx
DPS = int(os.environ.get("DPS", "80")); mp.mp.dps = DPS; PREC = int(DPS*3.4) + 60
L = float(sys.argv[1]); hk = float(sys.argv[2]); OUT = sys.argv[3]

def family(P):
    os.environ["P"] = str(P)
    import hpweil; importlib.reload(hpweil)
    B = hpweil.build(L, hk, DPS); m = B["m"]; N = int(mp.floor(mp.e**mp.mpf(L))); lam = hpweil.vm(N)
    Ci = mp.inverse(mp.cholesky(B["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci*M*Ci.T)
    Q0 = T(B["P"] - mp.log(mp.pi)*B["G"] + B["A"])
    Ms = {n: T(B["S"](mp.log(n))*(2/mp.sqrt(n))) for n in range(2, N + 1)}
    QL = Q0
    for n in range(2, N + 1):
        if lam[n] != 0: QL = QL - lam[n]*Ms[n]
    E, U = mp.eigsy(QL)
    W = mp.matrix(m, m)
    for c in range(m):
        for r in range(m): W[r, c] = U[r, c]/mp.sqrt(E[c])
    A = {n: (lambda X: (X + X.T)/2)(W.T*Ms[n]*W) for n in Ms}
    return dict(P=P, m=m, N=N, Ci=Ci, W=W, A=A, low=mp.nstr(min(E[i] for i in range(m)), 4))

def chol_logdet(M):
    k = M.nrows(); Lm = [[arb(0)]*k for _ in range(k)]; ld = arb(0)
    for j in range(k):
        s = M[j, j] - sum((Lm[j][p]*Lm[j][p] for p in range(j)), arb(0))
        if not (s > 0): return None
        Lm[j][j] = s.sqrt(); ld += 2*Lm[j][j].log()
        for i in range(j + 1, k): Lm[i][j] = (M[i, j] - sum((Lm[i][p]*Lm[j][p] for p in range(j)), arb(0)))/Lm[j][j]
    return ld

def barrier(args):
    blocks, n0i, sgn = args       # blocks: list over families of list over n of string matrices (scaled)
    ctx.prec = PREC
    As = [[arb_mat([[arb(x) for x in row] for row in Ab]) for Ab in fam] for fam in blocks]
    K = len(As[0]); Is = [arb_mat(F[0].nrows(), F[0].nrows(), [arb(1) if i == j else arb(0) for i in range(F[0].nrows()) for j in range(F[0].nrows())]) for F in As]
    def Ms(y):
        out = []
        for b, F in enumerate(As):
            M = Is[b]
            for a in range(K): M = M + F[a]*y[a]
            out.append(M.mid())
        return out
    def f(y, t):
        tot = -t*sgn*y[n0i]
        for M in Ms(y):
            ld = chol_logdet(M)
            if ld is None: return None
            tot -= ld
        return tot
    y = [arb(0)]*K; t = arb(1); kk = sum(F[0].nrows() for F in As)
    while True:
        for _ in range(200):
            g = [arb(0)]*K; H = arb_mat(K, K)
            for b, M in enumerate(Ms(y)):
                Mi = M.inv().mid(); Bs = [(Mi*Aa).mid() for Aa in As[b]]; k = M.nrows()
                for a in range(K): g[a] = g[a] - Bs[a].trace()
                V = arb_mat([[Bm[i, j] for i in range(k) for j in range(k)] for Bm in Bs])
                Ut = arb_mat([[Bm[j, i] for i in range(k) for j in range(k)] for Bm in Bs])
                H = (H + V*Ut.transpose()).mid()
            g[n0i] = g[n0i] - t*sgn
            d = H.solve(arb_mat([[-x] for x in g])).mid()
            dec = -sum((g[a]*d[a, 0] for a in range(K)), arb(0))
            if abs(dec.mid()) < arb(10)**(-30): break
            f0 = f(y, t); s = arb(1)
            while True:
                yn = [(y[a] + s*d[a, 0]).mid() for a in range(K)]; fn = f(yn, t)
                if fn is not None and fn <= f0 - s*dec/4: break
                s = s/2
                if s < arb(10)**(-60): break
            y = yn
        if arb(kk)/t < arb(10)**(-14)*max(arb(1), abs(y[n0i])): break
        t = t*4
    Xs = [(M.inv()*(1/t)).mid() for M in Ms(y)]
    return n0i, sgn, [[[Xb[i, j].str(DPS, radius=False) for j in range(Xb.ncols())] for i in range(Xb.nrows())] for Xb in Xs], y[n0i].mid().str(30, radius=False)

if __name__ == "__main__":
    t0 = time.time(); fams = [family(4), family(8)]
    N = min(F["N"] for F in fams); ns = list(range(2, N + 1))
    sc = {n: max(mp.sqrt(mp.fsum(F["A"][n][i, j]**2 for i in range(F["m"]) for j in range(F["m"]))) for F in fams) for n in ns}
    blocks = [[[[mp.nstr(F["A"][n][i, j]/sc[n], DPS) for j in range(F["m"])] for i in range(F["m"])] for n in ns] for F in fams]
    print(json.dumps(dict(stage="built", m=[F["m"] for F in fams], low=[F["low"] for F in fams], t=round(time.time() - t0))), flush=True)
    jobs = [(blocks, i, s) for i in range(len(ns)) for s in (1, -1)]
    with Pool(int(os.environ.get("NP", "8"))) as pool: res = pool.map(barrier, jobs)
    certs = []
    for n0i, sgn, Xl, yv in res:
        for b, F in enumerate(fams):
            X = mp.matrix([[mp.mpf(v) for v in row] for row in Xl[b]])
            Y = F["W"]*X*F["W"].T; Xsp = F["Ci"].T*Y*F["Ci"]; Xsp = (Xsp + Xsp.T)/2
            ev, V = mp.eigsy(Xsp); emax = max(abs(ev[i]) for i in range(F["m"]))
            parts = []
            for k in range(F["m"]):
                if ev[k] > emax*mp.mpf(10)**(-40):
                    parts.append(dict(w=mp.nstr(ev[k], 70), v=[mp.nstr(V[r, k], 70) for r in range(F["m"])]))
            certs.append(dict(target=ns[n0i], sgn=sgn, family=F["P"], approx=mp.nstr(mp.mpf(yv)/sc[ns[n0i]], 8), parts=parts))
    json.dump(dict(L=L, hk=hk, ns=ns, m=[F["m"] for F in fams], certs=certs), open(OUT, "w"))
    print(json.dumps(dict(stage="done", ncerts=len(certs), t=round(time.time() - t0))), flush=True)

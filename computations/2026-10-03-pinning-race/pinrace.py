# Pinning race: high-precision widths of W_L = {lam : Q_lam >= 0 on cubic-spline tests, supp f in [-L/2, L/2]}
# in coordinates delta_n = Lambda(n) - lam(n), n <= e^L.  Relaxation to the k lowest eigen-directions of Q_Lambda
# (fewer constraints => the reported widths are UPPER bounds on the true W_L widths).
import mpmath as mp, json, sys, time, os
from multiprocessing import Pool
from hpweil import build, vm
DPS = int(os.environ.get("DPS", "60")); mp.mp.dps = DPS

def chol_pd(M):
    try:
        mp.cholesky(M); return True
    except Exception:
        return False

def logdet(M):
    C = mp.cholesky(M); return 2*mp.fsum(mp.log(C[i, i]) for i in range(M.rows))

def barrier(args):
    Al, n0, sgn, dps = args
    mp.mp.dps = dps
    As = [mp.matrix([[mp.mpf(x) for x in row] for row in A]) for A in Al]
    K = len(As); k = As[0].rows; I = mp.eye(k)
    y = [mp.mpf(0)]*K
    Mof = lambda yy: I + sum((yy[n]*As[n] for n in range(K)), mp.zeros(k, k))
    t = mp.mpf(1); steps = 0
    while True:
        for _ in range(60):
            M = Mof(y); Mi = mp.inverse(M)
            Bs = [Mi*A for A in As]

            g = [-mp.fsum(Bs[n][i, i] for i in range(k)) for n in range(K)]
            g[n0] -= t*sgn
            H = mp.matrix(K, K)
            for a in range(K):
                for b in range(a, K):
                    v = mp.fsum(Bs[a][i, j]*Bs[b][j, i] for i in range(k) for j in range(k))
                    H[a, b] = v; H[b, a] = v
            d = mp.lu_solve(H, mp.matrix([-x for x in g]))
            dec = -mp.fsum(g[n]*d[n] for n in range(K))
            steps += 1
            if dec < mp.mpf(10)**(-30): break
            f0 = -t*sgn*y[n0] - logdet(M); s = mp.mpf(1)
            while True:
                yn = [y[n] + s*d[n] for n in range(K)]; Mn = Mof(yn)
                if chol_pd(Mn) and (-t*sgn*yn[n0] - logdet(Mn)) <= f0 - s*dec/4: break
                s /= 2
                if s < mp.mpf(10)**(-40): break
            y = yn
            if max(abs(v) for v in y) > mp.mpf(10)**40: return n0, sgn, "unbounded", steps
        if k/t < mp.mpf(10)**(-12)*max(1, abs(y[n0])): break
        t *= 8
    return n0, sgn, y[n0], steps

if __name__ == "__main__":
    L = float(sys.argv[1]); hk = float(sys.argv[2]); kk = int(sys.argv[3]); t0 = time.time()
    B = build(L, hk, DPS)
    m = B["m"]; N = int(mp.floor(mp.e**mp.mpf(L))); lam = vm(N)
    Ci = mp.inverse(mp.cholesky(B["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci*M*Ci.T)
    Q0 = T(B["P"] - mp.log(mp.pi)*B["G"] + B["A"])
    Ms = {n: T(B["S"](mp.log(n))*(2/mp.sqrt(n))) for n in range(2, N + 1)}
    QL = Q0
    for n in range(2, N + 1):
        if lam[n] != 0: QL = QL - lam[n]*Ms[n]
    E, U = mp.eigsy(QL)
    order = sorted(range(m), key=lambda i: E[i])
    ev = [E[i] for i in order]
    print(json.dumps(dict(stage="eig", L=L, m=m, N=N, t=round(time.time() - t0, 1), neg=sum(1 for e in ev if e < 0),
                          low=[mp.nstr(e, 3) for e in ev[:12]], top=mp.nstr(ev[-1], 3))), flush=True)
    if ev[0] <= 0:
        print(json.dumps(dict(stage="abort", reason="Q_Lambda not PD at this precision", low=mp.nstr(ev[0], 5)))); sys.exit(1)
    kk = min(kk, m); idx = order[:kk]
    W = mp.matrix(m, kk)
    for c, i in enumerate(idx):
        sc = 1/mp.sqrt(E[i])
        for r in range(m): W[r, c] = U[r, i]*sc
    As, scl = [], []
    for n in range(2, N + 1):
        X = W.T*Ms[n]*W; X = (X + X.T)/2
        s = mp.sqrt(mp.fsum(X[i, j]**2 for i in range(kk) for j in range(kk)))
        As.append(X/s); scl.append(s)
    single = {}
    for n in range(2, N + 1):
        e = mp.eigsy(As[n - 2], eigvals_only=True)
        lo = -1/max(e) if max(e) > 0 else -mp.inf; hi = -1/min(e) if min(e) < 0 else mp.inf
        single[n] = [mp.nstr(lo/scl[n - 2], 4), mp.nstr(hi/scl[n - 2], 4)]
    print(json.dumps(dict(stage="single", L=L, k=kk, t=round(time.time() - t0, 1), single=single)), flush=True)
    targets = [int(x) for x in os.environ.get("N0", "2,3,4,5").split(",") if int(x) <= N]
    Al = [[[mp.nstr(X[i, j], DPS + 5) for j in range(kk)] for i in range(kk)] for X in As]
    jobs = [(Al, n0 - 2, s, DPS) for n0 in targets for s in (1, -1)]
    with Pool(int(os.environ.get("NP", "8"))) as pool:
        res = pool.map(barrier, jobs)
    out = {}
    for n0i, s, v, st in res:
        n0 = n0i + 2
        out.setdefault(n0, {})["hi" if s == 1 else "lo"] = (v if isinstance(v, str) else mp.nstr(v/scl[n0i], 5))
        out[n0]["steps_%s" % ("hi" if s == 1 else "lo")] = st
    print(json.dumps(dict(stage="joint", L=L, k=kk, m=m, N=N, t=round(time.time() - t0, 1), joint=out)), flush=True)

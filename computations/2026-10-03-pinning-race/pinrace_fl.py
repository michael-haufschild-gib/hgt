# Pinning race, full spline space (no eigen-relaxation): high-precision log-barrier in python-flint (arb, midpoints).
# Coordinates delta_n = Lambda(n) - lam(n); W_L = {I + sum y_n A_n >= 0} in Q_Lambda-whitened coordinates.
import mpmath as mp, json, sys, time, os
from multiprocessing import Pool
from flint import arb_mat, arb, ctx
from hpweil import build, vm
DPS = int(os.environ.get("DPS", "80")); mp.mp.dps = DPS; PREC = int(DPS*3.4) + 40

def tomat(rows): return arb_mat([[arb(x) for x in r] for r in rows])

def cholesky_ok(M):
    k = M.nrows(); L = [[arb(0)]*k for _ in range(k)]
    for j in range(k):
        s = M[j, j] - sum((L[j][p]*L[j][p] for p in range(j)), arb(0))
        if not (s > 0): return None
        L[j][j] = s.sqrt()
        for i in range(j + 1, k):
            L[i][j] = (M[i, j] - sum((L[i][p]*L[j][p] for p in range(j)), arb(0)))/L[j][j]
    return sum(((2*L[j][j].log()) for j in range(k)), arb(0))

def barrier(args):
    Al, n0, sgn, prec, reg = args
    ctx.prec = prec; reg = arb(reg)
    As = [tomat(A) for A in Al]; K = len(As); k = As[0].nrows()
    I = arb_mat(k, k, [arb(1) if i == j else arb(0) for i in range(k) for j in range(k)])
    y = [arb(0)]*K; t = arb(1); steps = 0
    def Mof(yy):
        M = I
        for n in range(K): M = M + As[n]*yy[n]
        return M.mid()
    Bx = arb(os.environ.get("BOX", "1e8"))
    def fobj(yy, M):
        if any(not (abs(yy[n]) < Bx) for n in range(K) if n != n0): return None
        ld = cholesky_ok(M)
        if ld is None: return None
        return -t*sgn*yy[n0] - ld - sum(((Bx - yy[n]).log() + (Bx + yy[n]).log() for n in range(K) if n != n0), arb(0))
    while True:
        capped = True
        for _ in range(250):
            M = Mof(y); Mi = M.inv().mid()
            Bs = [(Mi*A).mid() for A in As]
            g = [-B.trace() + ((1/(Bx - y[n]) - 1/(Bx + y[n])) if n != n0 else 0) for n, B in enumerate(Bs)]; g[n0] = g[n0] - t*sgn
            V = arb_mat([[B[i, j] for i in range(k) for j in range(k)] for B in Bs])
            U = arb_mat([[B[j, i] for i in range(k) for j in range(k)] for B in Bs])
            H = (V*U.transpose()).mid()
            for n in range(K):
                if n != n0: H[n, n] = H[n, n] + 1/(Bx - y[n])**2 + 1/(Bx + y[n])**2
            d = H.solve(arb_mat([[-x] for x in g])).mid()
            dec = -sum((g[n]*d[n, 0] for n in range(K)), arb(0)); steps += 1
            if abs(dec.mid()) < arb(10)**(-24): capped = False; break
            f0 = fobj(y, M); s = arb(1)
            while True:
                yn = [(y[n] + s*d[n, 0]).mid() for n in range(K)]; fn = fobj(yn, Mof(yn))
                if fn is not None and fn <= f0 - s*dec/4: break
                s = s/2
                if s < arb(10)**(-60): break
            y = yn
            if abs(y[n0].mid()) > arb(10)**60: return n0, sgn, "unbounded", steps
        if arb(k + 2*(K - 1))/t < arb(10)**(-14)*max(arb(1), abs(y[n0])): break
        t = t*4
    yl = [v.mid().str(40, radius=False) for v in y]
    return n0, sgn, y[n0].mid().str(30, radius=False), (steps, capped, yl)

if __name__ == "__main__":
    L = float(sys.argv[1]); hk = float(sys.argv[2]); t0 = time.time()
    B = build(L, hk, DPS)
    m = B["m"]; N = int(mp.floor(mp.e**mp.mpf(L))); lam = vm(N)
    Ci = mp.inverse(mp.cholesky(B["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci*M*Ci.T)
    Q0 = T(B["P"] - mp.log(mp.pi)*B["G"] + B["A"])
    Ms = {n: T(B["S"](mp.log(n))*(2/mp.sqrt(n))) for n in range(2, N + 1)}
    QL = Q0
    for n in range(2, N + 1):
        if lam[n] != 0: QL = QL - lam[n]*Ms[n]
    E, U = mp.eigsy(QL); ev = sorted(E[i] for i in range(m))
    print(json.dumps(dict(stage="eig", L=L, m=m, N=N, t=round(time.time() - t0, 1), low=[mp.nstr(e, 3) for e in ev[:6]])), flush=True)
    if ev[0] <= 0: print(json.dumps(dict(stage="abort"))); sys.exit(1)
    W = mp.matrix(m, m)
    for c in range(m):
        sc = 1/mp.sqrt(E[c])
        for r in range(m): W[r, c] = U[r, c]*sc
    Al, scl = [], []
    for n in range(2, N + 1):
        X = W.T*Ms[n]*W; X = (X + X.T)/2
        s = mp.sqrt(mp.fsum(X[i, j]**2 for i in range(m) for j in range(m)))
        Al.append([[mp.nstr(X[i, j]/s, DPS) for j in range(m)] for i in range(m)]); scl.append(s)
    targets = [int(x) for x in os.environ.get("N0", "2,3,4,5").split(",") if int(x) <= N]
    reg = os.environ.get("REG", "1e-40")
    jobs = [(Al, n0 - 2, s, PREC, reg) for n0 in targets for s in (1, -1)]
    with Pool(int(os.environ.get("NP", "8"))) as pool:
        res = pool.map(barrier, jobs)
    out = {}
    for n0i, s, v, st in res:
        key = "hi" if s == 1 else "lo"
        out.setdefault(n0i + 2, {})[key] = v if v == "unbounded" else mp.nstr(mp.mpf(v)/scl[n0i], 5)
        out[n0i + 2]["steps_" + key] = st[:2]
        yy = [mp.mpf(v) for v in st[2]]
        Mm = mp.eye(m)
        for n in range(len(Al)): Mm += yy[n]*mp.matrix([[mp.mpf(x) for x in row] for row in Al[n]])
        out[n0i + 2]["mineig_" + key] = mp.nstr(min(mp.eigsy(Mm, eigvals_only=True)), 4)
        out[n0i + 2]["ymax_" + key] = mp.nstr(max(abs(v) for v in yy), 4)
    print(json.dumps(dict(stage="joint", L=L, m=m, N=N, t=round(time.time() - t0, 1), joint=out)), flush=True)

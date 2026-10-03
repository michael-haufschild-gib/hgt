# Joint pinning widths on the INTERSECTION of several spline-family LMIs (block-diagonal), flint log-barrier.
# Reports converged suprema (Newton centred, duality gap < tol) or flags non-convergence.
import json, sys, os, time
from multiprocessing import Pool
from flint import arb_mat, arb, ctx
PREC = int(os.environ.get("PREC", "300"))

def chol_logdet(M):
    k = M.nrows(); Lm = [[arb(0)]*k for _ in range(k)]; ld = arb(0)
    for j in range(k):
        s = M[j, j] - sum((Lm[j][p]*Lm[j][p] for p in range(j)), arb(0))
        if not (s > 0): return None
        Lm[j][j] = s.sqrt(); ld += 2*Lm[j][j].log()
        for i in range(j + 1, k):
            Lm[i][j] = (M[i, j] - sum((Lm[i][p]*Lm[j][p] for p in range(j)), arb(0)))/Lm[j][j]
    return ld

def solve(args):
    files, n0, sgn = args
    ctx.prec = PREC
    data = [json.load(open(f)) for f in files]
    N = min(d["N"] for d in data); ns = list(range(2, N + 1)); K = len(ns); i0 = ns.index(n0)
    blocks = []                                   # per family: list over n of arb_mat
    for d in data:
        blocks.append([arb_mat([[arb(x) for x in row] for row in d["blocks"][str(n)]]) for n in ns])
    sc = []
    for a in range(K):
        s = max(sum((abs(Ab[a][i, j]) for i in range(Ab[a].nrows()) for j in range(Ab[a].nrows())), arb(0)).mid() for Ab in blocks)
        sc.append(s)
    As = [[(Ab[a]/sc[a]).mid() for a in range(K)] for Ab in blocks]
    Is = [arb_mat(Ab[0].nrows(), Ab[0].nrows(), [arb(1) if i == j else arb(0) for i in range(Ab[0].nrows()) for j in range(Ab[0].nrows())]) for Ab in As]
    def Ms(y):
        out = []
        for b, Ab in enumerate(As):
            M = Is[b]
            for a in range(K): M = M + Ab[a]*y[a]
            out.append(M.mid())
        return out
    def f(y, t):
        tot = -t*sgn*y[i0]
        for M in Ms(y):
            ld = chol_logdet(M)
            if ld is None: return None
            tot -= ld
        return tot
    y = [arb(0)]*K; t = arb(1); steps = 0; kk = sum(Ab[0].nrows() for Ab in As)
    while True:
        cent = False
        for _ in range(200):
            g = [arb(0)]*K; H = arb_mat(K, K)
            for b, M in enumerate(Ms(y)):
                Mi = M.inv().mid(); Bs = [(Mi*A).mid() for A in As[b]]; k = M.nrows()
                for a in range(K): g[a] = g[a] - Bs[a].trace()
                V = arb_mat([[B[i, j] for i in range(k) for j in range(k)] for B in Bs])
                U = arb_mat([[B[j, i] for i in range(k) for j in range(k)] for B in Bs])
                H = (H + V*U.transpose()).mid()
            g[i0] = g[i0] - t*sgn
            d = H.solve(arb_mat([[-x] for x in g])).mid()
            dec = -sum((g[a]*d[a, 0] for a in range(K)), arb(0)); steps += 1
            if abs(dec.mid()) < arb(10)**(-24): cent = True; break
            f0 = f(y, t); s = arb(1)
            while True:
                yn = [(y[a] + s*d[a, 0]).mid() for a in range(K)]; fn = f(yn, t)
                if fn is not None and fn <= f0 - s*dec/4: break
                s = s/2
                if s < arb(10)**(-50): break
            if s < arb(10)**(-50): break
            y = yn
            if max(abs(v.mid()) for v in y) > arb(10)**30: return n0, sgn, "diverged", steps, False
        if not cent: return n0, sgn, (y[i0]/sc[i0]).mid().str(20, radius=False), steps, False
        if arb(kk)/t < arb(10)**(-12)*max(arb(1), abs(y[i0])): break
        t = t*4
    return n0, sgn, (y[i0]/sc[i0]).mid().str(20, radius=False), steps, True

if __name__ == "__main__":
    files = sys.argv[1].split(","); n0s = [int(x) for x in sys.argv[2].split(",")]
    jobs = [(files, n0, s) for n0 in n0s for s in (1, -1)]
    with Pool(int(os.environ.get("NP", "8"))) as pool: res = pool.map(solve, jobs)
    out = {}
    for n0, s, v, st, ok in res:
        key = "hi" if s == 1 else "lo"; out.setdefault(n0, {})[key] = v; out[n0][key + "_ok"] = ok; out[n0][key + "_steps"] = st
    print(json.dumps(dict(files=files, joint=out)))

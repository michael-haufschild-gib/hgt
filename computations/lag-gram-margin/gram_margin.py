import numpy as np, math, json, sys, time
from concurrent.futures import ProcessPoolExecutor
# Arithmetic Gram matrix G_N[n,m] = Phi(log(n/m)), Phi via the genus-kernel explicit formula at X = n/m >= 1.
def lam_table(N):
    spf = np.zeros(N + 1, dtype=np.int64)
    for p in range(2, int(N ** 0.5) + 1):
        if spf[p] == 0:
            spf[p*p::p][spf[p*p::p] == 0] = p
    idx = np.arange(N + 1); spf[spf == 0] = idx[spf == 0]; spf[0] = 0; spf[1] = 0
    Lam = np.zeros(N + 1); q = idx.copy(); p = spf.copy(); mask = np.ones(N + 1, dtype=bool); mask[:2] = False
    for _ in range(40):
        sel = mask & (q > 1) & (q % np.where(p > 0, p, 1) == 0)
        if not sel.any(): break
        q[sel] //= p[sel]
    ispp = mask & (q == 1); Lam[ispp] = np.log(p[ispp].astype(float))
    return Lam
gamma = 0.5772156649015328606
c0 = 2 + gamma - math.log(4 * math.pi)
def S(X):
    # closed form of sum_{k>=1} X^{-2k}/(2k(2k+1)) for X > 1
    return 1.0 - 0.5 * math.log1p(-X ** (-2.0)) - X * math.atanh(1.0 / X)
def phi_of_X(X, psi_floor, M_floor):
    # X >= 1 real; psi_floor, M_floor at floor(X)
    if X < 1.0000000001: return c0
    return ((X - psi_floor) + X * (M_floor - math.log(X) + gamma) - math.log(2 * math.pi) + S(X)) / math.sqrt(X)
def gram(N, Lam):
    psi = np.cumsum(Lam); M = np.cumsum(Lam / np.maximum(np.arange(N + 1), 1))
    G = np.zeros((N, N))
    for n in range(1, N + 1):
        for m in range(1, n + 1):
            X = n / m; f = n // m
            v = phi_of_X(X, psi[f], M[f])
            G[n-1, m-1] = v; G[m-1, n-1] = v
    return G
def margin(N):
    Lam = lam_table(N)
    G = gram(N, Lam)
    w = np.linalg.eigvalsh(G)
    return N, float(w[0]), float(w[1]), float(w[-1]), float(np.trace(G)), int((w < -1e-9).sum())
if __name__ == "__main__":
    Ns = [int(x) for x in sys.argv[1:]] or [50, 100, 200, 400, 800, 1600]
    t0 = time.time()
    with ProcessPoolExecutor(max_workers=min(8, len(Ns))) as ex:
        res = list(ex.map(margin, Ns))
    out = {"c0": c0, "rows": [{"N": r[0], "lam_min": r[1], "lam_2": r[2], "lam_max": r[3], "trace": r[4], "neg_count": r[5]} for r in res], "time_s": time.time() - t0}
    print(json.dumps(out, indent=1), flush=True)
    # two-prime Toeplitz form on Z^2: entries Phi(k log2 + l log3) for |k|,|l|<=K, via prime side with X = 2^k 3^l (use symmetry Phi even)
    def phi_lag(L, Lam, psi, M):
        X = math.exp(abs(L)); f = int(math.floor(X + 1e-12))
        return phi_of_X(X, psi[f], M[f])
    rows2 = []
    for K in [2, 3, 4, 5]:
        Lam = lam_table(6 ** (2 * K) + 2)
        psi = np.cumsum(Lam); M = np.cumsum(Lam / np.maximum(np.arange(len(Lam)), 1))
        pts = [(k, l) for k in range(-K, K + 1) for l in range(-K, K + 1)]
        n = len(pts); T = np.zeros((n, n))
        for i, (k1, l1) in enumerate(pts):
            for j, (k2, l2) in enumerate(pts):
                if j > i: continue
                L = (k1 - k2) * math.log(2) + (l1 - l2) * math.log(3)
                v = phi_lag(L, Lam, psi, M); T[i, j] = v; T[j, i] = v
        w = np.linalg.eigvalsh(T)
        rows2.append({"K": K, "dim": n, "lam_min": float(w[0]), "lam_max": float(w[-1]), "neg_count": int((w < -1e-9).sum())})
    print(json.dumps({"two_prime_rows": rows2, "time_s": time.time() - t0}, indent=1), flush=True)

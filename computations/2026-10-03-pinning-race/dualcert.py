# Extract the n0-selective dual certificate g* (central-path X = M^{-1}/t) of the pinning SDP and compare its
# transform with |Xi|^2:  is g* ~ K_Phi * h (Riemann-kernel based) ?
import mpmath as mp, json, sys, os, time
from hpweil import build, vm, P
DPS = int(os.environ.get("DPS", "70")); mp.mp.dps = DPS

def central(As, n0, sgn, tmax):
    K = len(As); k = As[0].rows; I = mp.eye(k); y = [mp.mpf(0)]*K
    Mof = lambda yy: I + sum((yy[n]*As[n] for n in range(K)), mp.zeros(k, k))
    t = mp.mpf(1)
    while t < tmax:
        for _ in range(60):
            M = Mof(y); Mi = mp.inverse(M); Bs = [Mi*A for A in As]
            g = [-mp.fsum(Bs[n][i, i] for i in range(k)) for n in range(K)]; g[n0] -= t*sgn
            H = mp.matrix(K, K)
            for a in range(K):
                for b in range(a, K):
                    v = mp.fsum(Bs[a][i, j]*Bs[b][j, i] for i in range(k) for j in range(k)); H[a, b] = v; H[b, a] = v
            d = mp.lu_solve(H, mp.matrix([-x for x in g])); dec = -mp.fsum(g[n]*d[n] for n in range(K))
            if dec < mp.mpf(10)**(-30): break
            ld = lambda MM: 2*mp.fsum(mp.log(mp.cholesky(MM)[i, i]) for i in range(k))
            f0 = -t*sgn*y[n0] - ld(M); s = mp.mpf(1)
            while True:
                yn = [y[n] + s*d[n] for n in range(K)]
                try:
                    Mn = Mof(yn); fn = -t*sgn*yn[n0] - ld(Mn)
                    if fn <= f0 - s*dec/4: break
                except Exception: pass
                s /= 2
            y = yn
        t *= 8
    M = Mof(y); return y, mp.inverse(M)/(t/8)

if __name__ == "__main__":
    L, hk, kk, n0, sgn = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    B = build(L, hk, DPS); m = B["m"]; N = int(mp.floor(mp.e**mp.mpf(L))); lam = vm(N)
    Ci = mp.inverse(mp.cholesky(B["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci*M*Ci.T)
    Q0 = T(B["P"] - mp.log(mp.pi)*B["G"] + B["A"])
    Ms = {n: T(B["S"](mp.log(n))*(2/mp.sqrt(n))) for n in range(2, N + 1)}
    QL = Q0
    for n in range(2, N + 1):
        if lam[n] != 0: QL = QL - lam[n]*Ms[n]
    E, U = mp.eigsy(QL); order = sorted(range(m), key=lambda i: E[i]); idx = order[:kk]
    W = mp.matrix(m, kk)
    for c, i in enumerate(idx):
        for r in range(m): W[r, c] = U[r, i]/mp.sqrt(E[i])
    As, scl = [], []
    for n in range(2, N + 1):
        X = W.T*Ms[n]*W; X = (X + X.T)/2; s = mp.sqrt(mp.fsum(X[i, j]**2 for i in range(kk) for j in range(kk)))
        As.append(X/s); scl.append(s)
    y, XV = central(As, n0 - 2, sgn, mp.mpf(10)**14)
    Xs = Ci.T*(W*XV*W.T)*Ci                      # dual certificate in spline coefficients
    hkm, xs = B["hk"], B["xs"]
    def ghat(t):
        if t == 0: b = [hkm for x in xs]
        else:
            z = t*hkm/2; sc = hkm*(mp.sin(z)/z)**P; b = [sc*mp.expj(t*x) for x in xs]
        return mp.re(mp.fsum(Xs[i, j]*b[i]*mp.conj(b[j]) for i in range(m) for j in range(m)))
    def gx(x): return mp.fsum(Xs[i, j]*B["S"].__closure__ and 0 for i in range(1) for j in range(1))
    Sx = {n: B["S"](mp.log(n)) for n in range(2, N + 1)}
    sel = {n: mp.nstr(mp.fsum(Xs[i, j]*Sx[n][i, j] for i in range(m) for j in range(m))*2/mp.sqrt(n), 5) for n in range(2, N + 1)}
    def Xi(t):
        s = mp.mpf(1)/2 + 1j*t
        return mp.re(s*(s - 1)/2*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s))
    rows = []
    for j in range(0, 161):
        t = mp.mpf(j)/2; gh = ghat(t); xi = Xi(t)
        rows.append([float(t), mp.nstr(gh, 6), mp.nstr(xi**2, 6), mp.nstr(gh/xi**2, 6) if xi != 0 else "inf"])
    print(json.dumps(dict(L=L, hk=hk, P=P, m=m, n0=n0, sgn=sgn, width=mp.nstr(y[n0 - 2]/scl[n0 - 2], 6), selectivity=sel, rows=rows)))

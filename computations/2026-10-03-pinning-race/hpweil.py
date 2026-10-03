# High-precision Weil form on the cubic B-spline span (mpmath), then preconditioned double SDP for pinning intervals.
# arch(g) = -gamma g(0) + 2 int_0^inf [g(0) e^{-2x} - e^{-x/2} g(x)] / (1 - e^{-2x}) dx   (from psi integral rep.)
import mpmath as mp, numpy as np, cvxpy as cp, json, sys, time
from multiprocessing import Pool
mp.mp.dps = 40

def B8(u):
    u = abs(mp.mpf(u))
    if u >= 4: return mp.mpf(0)
    x = u + 4; s = mp.mpf(0)
    for j in range(9):
        if x - j > 0: s += (-1)**j*mp.binomial(8, j)*(x - j)**7
    return s/5040

def gfun(D, x, hk):     # symmetrized autocorrelation kernel entry: (hk/2)[B8((D-x)/hk) + B8((-D-x)/hk)]
    return hk/2*(B8((D - x)/hk) + B8((-D - x)/hk))

def arch_lag(args):
    k, hk, dps = args
    mp.mp.dps = dps
    hk = mp.mpf(hk); D = k*hk
    g0 = gfun(D, 0, hk)
    f = lambda x: (g0*mp.e**(-2*x) - mp.e**(-x/2)*gfun(D, x, hk))/(1 - mp.e**(-2*x))
    pts = sorted(set([mp.mpf(0)] + [abs(D + j*hk) for j in range(-4, 5)] + [abs(-D + j*hk) for j in range(-4, 5)]))
    pts = [p for p in pts if p >= 0] + [mp.inf]
    val = -mp.euler*g0 + 2*mp.quad(f, pts)
    return k, val

def build(L, hk, dps=40):
    mp.mp.dps = dps
    hkm = mp.mpf(hk)
    m = int(round(L/hk)) - 3; hkm = mp.mpf(L)/(m + 3)
    xs = [-mp.mpf(L)/2 + 2*hkm + hkm*i for i in range(m)]
    with Pool(8) as pool:
        res = dict(pool.map(arch_lag, [(k, hkm, dps) for k in range(m)]))
    A = mp.matrix(m, m); G = mp.matrix(m, m)
    for i in range(m):
        for j in range(m):
            A[i, j] = res[abs(i - j)]; G[i, j] = hkm*B8((xs[i] - xs[j])/hkm)
    def Fvec(a):
        z = a*hkm/2; return [hkm*mp.e**(a*x)*(mp.sinh(z)/z)**4 for x in xs]
    u, v = Fvec(mp.mpf(1)/2), Fvec(-mp.mpf(1)/2)
    P = mp.matrix(m, m)
    for i in range(m):
        for j in range(m): P[i, j] = u[i]*v[j] + v[i]*u[j]
    def S(x):
        M = mp.matrix(m, m)
        for i in range(m):
            for j in range(m): M[i, j] = gfun(xs[i] - xs[j], x, hkm)
        return M
    return dict(m=m, hk=hkm, xs=xs, A=A, G=G, P=P, S=S)

def vm(N):
    lam = [mp.mpf(0)]*(N + 1)
    for p in range(2, N + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= N: lam[pk] = mp.log(p); pk *= p
    return lam

if __name__ == "__main__":
    L = float(sys.argv[1]); hk = float(sys.argv[2]); t0 = time.time()
    B = build(L, hk)
    m = B["m"]; N = int(np.floor(np.exp(L))); lam = vm(N)
    Cl = mp.cholesky(B["G"]); Ci = mp.inverse(Cl)
    T = lambda M: (lambda X: (X + X.T)/2)(Ci*M*Ci.T)
    Q0 = T(B["P"] - mp.log(mp.pi)*B["G"] + B["A"])
    Ms = {n: T(B["S"](mp.log(n))*(2/mp.sqrt(n))) for n in range(2, N + 1)}
    QL = Q0
    for n in range(2, N + 1):
        if lam[n] != 0: QL = QL - lam[n]*Ms[n]
    E, U = mp.eigsy(QL)
    mu = [E[i] for i in range(m)]
    order = sorted(range(m), key=lambda i: mu[i])
    print(json.dumps(dict(stage="eig", L=L, hk=hk, m=m, t=round(time.time() - t0, 1),
                          mu=[mp.nstr(mu[i], 4) for i in order[:6]])), flush=True)
    Dm = [1/mp.sqrt(mu[i]) if mu[i] > 0 else mp.mpf(0) for i in range(m)]
    def pre(M):
        X = U.T*M*U
        return np.array([[float(Dm[i]*X[i, j]*Dm[j]) for j in range(m)] for i in range(m)])
    Ns = [pre(Ms[n]) for n in range(2, N + 1)]
    Ns = [(X + X.T)/2 for X in Ns]
    np.savez('pre_L%s_hk%s.npz' % (L, hk), *Ns)
    import os
    if os.environ.get('ONLYSAVE'): sys.exit(0)
    sc = np.array([np.linalg.norm(X, 2) for X in Ns]); Ns = [X/s for X, s in zip(Ns, sc)]
    y = cp.Variable(len(Ns))
    cons = [np.eye(m) - sum(y[i]*Ns[i] for i in range(len(Ns))) >> 0]
    out = {}
    for t in range(2, N + 1):
        i = t - 2; res = []
        for sense in (cp.Minimize, cp.Maximize):
            prob = cp.Problem(sense(y[i]), cons)
            val = "err"
            for solver, kw in ((cp.CLARABEL, dict(max_iter=2000)), (cp.SCS, dict(eps=1e-10, max_iters=500000)), (cp.CLARABEL, dict(max_iter=4000, static_regularization_constant=1e-7))):
                try:
                    prob.solve(solver=solver, **kw)
                    if prob.status in ("optimal", "optimal_inaccurate"):
                        val = float(prob.value)/sc[i]; break
                    else:
                        val = prob.status
                except Exception:
                    continue
            res.append(val)
        out[t] = res
    print(json.dumps(dict(stage="intervals", L=L, hk=hk, Lambda=[float(lam[n]) for n in range(2, N + 1)], iv=out, t=round(time.time() - t0, 1))), flush=True)

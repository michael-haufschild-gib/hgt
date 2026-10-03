# High-precision Weil form on the cubic B-spline span (mpmath), then preconditioned double SDP for pinning intervals.
# arch(g) = -gamma g(0) + 2 int_0^inf [g(0) e^{-2x} - e^{-x/2} g(x)] / (1 - e^{-2x}) dx   (from psi integral rep.)
import mpmath as mp, json, sys, time, os
from multiprocessing import Pool
mp.mp.dps = 40
P = int(os.environ.get("P", "4"))        # B-spline order of the test basis (4 = cubic); autocorrelation has order 2P
Q = 2*P

def B8(u):                                # centred cardinal B-spline of order Q = 2P, support [-P, P]
    u = abs(mp.mpf(u))
    if u >= P: return mp.mpf(0)
    x = u + P; s = mp.mpf(0)
    for j in range(Q + 1):
        if x - j > 0: s += (-1)**j*mp.binomial(Q, j)*(x - j)**(Q - 1)
    return s/mp.factorial(Q - 1)

def gfun(D, x, hk):     # symmetrized autocorrelation kernel entry: (hk/2)[B8((D-x)/hk) + B8((-D-x)/hk)]
    return hk/2*(B8((D - x)/hk) + B8((-D - x)/hk))

def arch_lag(args):
    k, hk, dps = args
    mp.mp.dps = dps
    hk = mp.mpf(hk); D = k*hk
    g0 = gfun(D, 0, hk)
    f = lambda x: (g0*mp.e**(-2*x) - mp.e**(-x/2)*gfun(D, x, hk))/(1 - mp.e**(-2*x))
    pts = sorted(set([mp.mpf(0)] + [abs(D + j*hk) for j in range(-P, P + 1)] + [abs(-D + j*hk) for j in range(-P, P + 1)]))
    pts = [p for p in pts if p >= 0] + [mp.inf]
    val = -mp.euler*g0 + 2*mp.quad(f, pts)
    return k, val

def build(L, hk, dps=40):
    mp.mp.dps = dps
    hkm = mp.mpf(hk)
    m = int(round(L/hk)) - (P - 1); hkm = mp.mpf(L)/(m + P - 1)
    xs = [-mp.mpf(L)/2 + hkm*P/2 + hkm*i for i in range(m)]
    with Pool(8) as pool:
        res = dict(pool.map(arch_lag, [(k, hkm, dps) for k in range(m)]))
    A = mp.matrix(m, m); G = mp.matrix(m, m)
    for i in range(m):
        for j in range(m):
            A[i, j] = res[abs(i - j)]; G[i, j] = hkm*B8((xs[i] - xs[j])/hkm)
    def Fvec(a):
        z = a*hkm/2; return [hkm*mp.e**(a*x)*(mp.sinh(z)/z)**P for x in xs]
    u, v = Fvec(mp.mpf(1)/2), Fvec(-mp.mpf(1)/2)
    PM = mp.matrix(m, m)
    for i in range(m):
        for j in range(m): PM[i, j] = u[i]*v[j] + v[i]*u[j]
    def S(x):
        M = mp.matrix(m, m)
        for i in range(m):
            for j in range(m): M[i, j] = gfun(xs[i] - xs[j], x, hkm)
        return M
    return dict(m=m, hk=hkm, xs=xs, A=A, G=G, P=PM, S=S)

def vm(N):
    lam = [mp.mpf(0)]*(N + 1)
    for p in range(2, N + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= N: lam[pk] = mp.log(p); pk *= p
    return lam


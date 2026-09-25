# Cumulants of the statistic w = log x under the tilted theta measures x^{2s} Phi(x) dx on (0,inf).
# Phi(x) = sum_n (2 pi^2 n^4 e^{9x/2} - 3 pi n^2 e^{5x/2}) e^{-pi n^2 e^{2x}}  (Riemann's kernel, Xi(t) = int Phi cos(tx))
# Question: do the cumulants kappa_k(w), k>=3, alternate in sign ((-1)^k kappa_k > 0) for every tilt s >= 0?
# Also the single-atom kernel (n = 1 only).  Guidance only.
import mpmath as mp, sys
mp.mp.dps = 40
def Phi(x, atoms=60):
    e2 = mp.e**(2*x)
    return mp.fsum((2*mp.pi**2*n**4*mp.e**(9*x/2) - 3*mp.pi*n**2*mp.e**(5*x/2))*mp.e**(-mp.pi*n**2*e2) for n in range(1, atoms+1))
def Phi1(x):
    e2 = mp.e**(2*x)
    return (2*mp.pi**2*mp.e**(9*x/2) - 3*mp.pi*mp.e**(5*x/2))*mp.e**(-mp.pi*e2)
def moments(s, kern, K=8):
    # raw moments of w = log x under x^{2s} kern(x) dx, using x = e^w substitution: int w^k e^{(2s+1)w} kern(e^w) dw
    f = lambda w, k: (w**k) * mp.e**((2*s+1)*w) * kern(mp.e**w)
    pts = [-40, -10, -3, -1, 0, 0.5, 1, 1.5, 2, 3]
    Z = mp.quad(lambda w: f(w, 0), pts)
    return [mp.quad(lambda w: f(w, k), pts)/Z for k in range(K+1)]
def cumulants(m):
    # from raw moments (m[0]=1) via recursion
    K = len(m)-1
    kap = [mp.mpf(0)]*(K+1)
    for n in range(1, K+1):
        kap[n] = m[n] - mp.fsum(mp.binomial(n-1, k-1)*kap[k]*m[n-k] for k in range(1, n))
    return kap
for name, kern in [("full", Phi), ("atom1", Phi1)]:
    print("==", name)
    for s in [0, 0.25, 0.5, 1, 2, 3, 5, 10, 20, 50, 100]:
        kap = cumulants(moments(mp.mpf(s), kern))
        signs = "".join("+" if kap[k] > 0 else "-" for k in range(2, 9))
        print(f"s={s:6}: k2..k8 signs {signs}  " + " ".join(mp.nstr(kap[k], 6) for k in range(2, 9)))
        sys.stdout.flush()

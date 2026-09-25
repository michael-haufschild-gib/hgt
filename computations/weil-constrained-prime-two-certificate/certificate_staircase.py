#!/usr/bin/env python3
"""Staircase certificate: m_S >= m_stair (step function with band minima), low modes deg<N on V0,
 archimedean form and full form with the prime 2 (S in (log2, log3)): prime term = -sqrt2 log2 <f, T_{log2} f>."""
import numpy as np, math
from scipy import integrate, special
exec(open('constrained_multiplier.py').read().split('for S in (0.5')[0])
xs = np.linspace(0, 400, 40001); w = np.ones_like(xs); w[0]=w[-1]=0.5; w*=xs[1]-xs[0]
def band_gram(S, N, lo, hi, jn):
    a = S/2; G = np.zeros((N, N))
    for n in range(N):
        for k in range(n, N):
            if (n-k)%2: continue
            ph = (-1)**((n-k)//2)
            G[n,k]=G[k,n] = (2/(2*math.pi))*np.sum(w*((xs>lo)&(xs<=hi))*jn[n]*jn[k])*(2*a)**2*math.sqrt((2*n+1)*(2*k+1))/(2*a)*ph
    return G
def prime2_gram(S, N):
    a = S/2; u = math.log(2)
    if u >= S: return np.zeros((N, N))
    xg = np.linspace(-a, a, 20001); dx = xg[1]-xg[0]
    P = np.array([math.sqrt((2*n+1)/(2*a))*special.eval_legendre(n, xg/a) for n in range(N)])
    # <p_n, T_u p_k> = int p_n(x) p_k(x-u) dx over the overlap x in [u-a, a]
    shift = int(round(u/dx))
    G = np.zeros((N, N))
    for n in range(N):
        for k in range(N):
            G[n,k] = np.sum(P[n][shift:]*P[k][:len(xg)-shift])*dx
    return 0.5*(G + G.T)   # symmetrized: <f, T_u f> = f^T G f
def tau(N, a, xi): return 2*a**(2*N+1)*xi**(2*N)/(math.factorial(N)**2*(2*N+1))
edges = [0] + [5.0 + 0.5*k for k in range(23)] + [1e9]   # 5.0..16.0 step 0.5, last band [16,inf)
for S in (math.log(2), 0.72, 0.75, 0.8, 0.85, 0.9, 1.0):
    a = S/2
    xm = np.linspace(0, 400, 8001); ms = np.array([m(S, x) for x in xm])
    cs = [ms[(xm > lo) & (xm <= hi)].min() if hi < 1e8 else ms[xm > lo].min() for lo, hi in zip(edges[:-1], edges[1:])]
    cs[0] = A(S)   # exact minimum on the first band (Lambda >= 0)
    Nmin = int(math.ceil(2.9*a*16.0)) + 2
    for N in (max(16, Nmin),):
        jn = np.array([special.spherical_jn(n, a*xs) for n in range(N)])
        Mst = sum(c*band_gram(S, N, lo, hi, jn) for c, lo, hi in zip(cs[:-1], edges[:-2], edges[1:-1])) + cs[-1]*(np.eye(N) - band_gram(S, N, 0, edges[-2], jn))
        C = constraints(S, N); u_, s_, vt = np.linalg.svd(C); Bn = vt[2:].T
        lam_arch = np.linalg.eigvalsh(Bn.T @ Mst @ Bn)[0]
        Mlow = 2*integrate.quad(lambda x: tau(N, a, x), 0, edges[-2])[0]/(2*math.pi)
        cmax = max(abs(c) for c in cs)
        kappa_high = cs[-1]*(1 - Mlow) - cmax*Mlow - cmax*math.sqrt(Mlow)
        kappa_low = lam_arch - cmax*math.sqrt(Mlow)
        line = "S=%.4f N=%d c0=%.3f c_last=%.3f | low-mode arch cert=%.4f | high-mode=%.4f (Mlow=%.1e)" % (S, N, cs[0], cs[-1], kappa_low, kappa_high, Mlow)
        if S > math.log(2):
            P2 = prime2_gram(S, N)
            lam_full = np.linalg.eigvalsh(Bn.T @ (Mst - math.sqrt(2)*math.log(2)*P2) @ Bn)[0]
            line += " | with prime 2: low-mode cert=%.4f, high-mode cert=%.4f" % (lam_full - cmax*math.sqrt(Mlow), kappa_high - math.sqrt(2)*math.log(2))
        print(line)

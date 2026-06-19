import mpmath as mp
import numpy as np

mp.mp.dps = 30
Ls = [5, 10, 20, 30, 40]
# first 40 zeta ordinates
G = [float(mp.zetazero(k).imag) for k in range(1, 41)]

def cond_for(points, L):
    g = points[:L]
    n = np.arange(1, L+1)
    # V[j,n] = n^{-i g_j} = exp(-i g_j log n)
    V = np.exp(-1j * np.outer(g, np.log(n)))
    s = np.linalg.svd(V, compute_uv=False)
    return s[0], s[-1], s[0]/s[-1]

# control 1: equispaced at mean zeta gap near the same range
# control 2: random uniform in [g_1, g_L] (same span)
rng = np.random.default_rng(12345)
print(f"{'L':>3} | {'zeta smin':>11} {'zeta cond':>11} | {'equi smin':>11} {'equi cond':>11} | {'rand smin':>11} {'rand cond':>11}")
for L in Ls:
    smax_z, smin_z, cond_z = cond_for(G, L)
    span = G[L-1]-G[0]
    equi = list(np.linspace(G[0], G[L-1], L))
    smax_e, smin_e, cond_e = cond_for(equi, L)
    rnd = sorted(rng.uniform(G[0], G[L-1], L))
    smax_r, smin_r, cond_r = cond_for(rnd, L)
    print(f"{L:>3} | {smin_z:>11.3e} {cond_z:>11.3e} | {smin_e:>11.3e} {cond_e:>11.3e} | {smin_r:>11.3e} {cond_r:>11.3e}")
print()
print("note: smin normalized by smax=%.3f (=sqrt(L) scale); cond=smax/smin. Lower cond = better conditioned = more 'generic'." % np.linalg.svd(np.exp(-1j*np.outer(G[:5],np.log(np.arange(1,6)))),compute_uv=False)[0])

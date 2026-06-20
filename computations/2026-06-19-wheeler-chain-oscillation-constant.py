#!/usr/bin/env python3
# Wheeler 2026-06-19 — FE-symmetric secular chain (Professor id=409): x_rho = 1/(rho(1-rho)) = 1/(1/4+gamma^2).
# moments sigma_k = sum (1/4+gamma^2)^{-k} (Keiper-Li secondary sums) -> Jacobi -> a_n -> e_n=a_n-1/4.
# Test the DERIVED oscillation constant: e_n ~ lambda/n^2, RH <=> lambda <= 1/4 (discrete Hardy/Chihara).
# Output n^2*e_n (-> lambda) to estimate the subleading coefficient.
import mpmath as mp
mp.mp.dps = 60

def cheb(m, M):
    L = len(m)
    sig_old = [mp.mpf(0)]*L
    sig = list(m)
    alpha = [mp.mpf(0)]*M; beta = [mp.mpf(0)]*M
    alpha[0] = m[1]/m[0]; beta[0] = m[0]
    for k in range(1, M):
        newsig = [mp.mpf(0)]*L
        for l in range(k, L-k):
            newsig[l] = sig[l+1] - alpha[k-1]*sig[l] - beta[k-1]*sig_old[l]
        alpha[k] = newsig[k+1]/newsig[k] - sig[k]/sig[k-1]
        beta[k]  = newsig[k]/sig[k-1]
        sig_old, sig = sig, newsig
    return alpha, beta

N = 120
M = 11
print("computing %d zeta zeros (dps=60, FE-symmetric coord)..." % N, flush=True)
gam = [mp.im(mp.zetazero(n)) for n in range(1, N+1)]
xs = [1/(mp.mpf(1)/4 + g**2) for g in gam]; ws = [mp.mpf(2)]*N
L = 2*M
m = [sum(w*x**l for x, w in zip(xs, ws)) for l in range(L)]
alpha, beta = cheb(m, M)
# a_n = beta_n/(alpha_{n-1} alpha_n); e_n = a_n - 1/4; g_n minimal param
g = [mp.mpf(0)]*M
print("\n n :       a_n            e_n=a_n-1/4      n^2*e_n (->lambda)      g_n")
for n in range(1, M):
    a = beta[n]/(alpha[n-1]*alpha[n])
    e = a - mp.mpf(1)/4
    g[n] = a/(1 - g[n-1])
    print("%2d : %s   %s   %s   %s" % (n, mp.nstr(a,10), mp.nstr(e,8), mp.nstr(n*n*e,8), mp.nstr(g[n],8)))
print("\nDERIVED criterion: RH <=> sum_{j<=n} j(j+1) e_j < (n+1)/4 ; e_n~lambda/n^2 => lambda<=1/4.")
S = mp.mpf(0)
print("\n n :  partial sum_{j<=n} j(j+1)e_j      (n+1)/4        ratio (->4*lambda)")
gg = [mp.mpf(0)]*M
for n in range(1, M):
    a = beta[n]/(alpha[n-1]*alpha[n]); e = a - mp.mpf(1)/4
    S += n*(n+1)*e
    bound = (n+1)/mp.mpf(4)
    print("%2d : %s        %s        %s" % (n, mp.nstr(S,8), mp.nstr(bound,6), mp.nstr(S/bound,6)))
print("\nDONE", flush=True)

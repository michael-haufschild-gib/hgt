#!/usr/bin/env python3
# Wheeler 2026-06-19 — pre-certify the chain-sequence diagnostic (worklog-professor §914-941):
# secular measure mu = sum_rho delta_{x_rho}, x_rho = u_rho^{-2}, u_rho=(rho-1/2)/i = gamma (REAL iff RH).
# moments m_l = sum w x^l ; Chebyshev algorithm -> Jacobi (b_n=alpha_n, lambda_n=beta_n);
# a_n = lambda_n/(b_{n-1} b_n); g_0=0, g_n = a_n/(1-g_{n-1}); chain <=> g_n in [0,1) all n; no-margin g_n->1/2.
# RH side: real gamma -> positive measure -> g_n in [0,1). OFF-LINE side: one zero moved off the line
# (x complex) -> g_n must EXIT [0,1) / go complex at finite n (the DH separator).
import mpmath as mp
mp.mp.dps = 50

def cheb(m, M):
    # plain Chebyshev algorithm: moments m[0..2M-1] -> alpha[0..M-1], beta[0..M-1]
    L = len(m)
    sig_old = [mp.mpf(0)]*L
    sig = list(m)                       # sigma_0
    alpha = [mp.mpf(0)]*M
    beta  = [mp.mpf(0)]*M
    alpha[0] = m[1]/m[0]
    beta[0]  = m[0]
    for k in range(1, M):
        newsig = [mp.mpf(0)]*L
        for l in range(k, L-k):
            newsig[l] = sig[l+1] - alpha[k-1]*sig[l] - beta[k-1]*sig_old[l]
        alpha[k] = newsig[k+1]/newsig[k] - sig[k]/sig[k-1]
        beta[k]  = newsig[k]/sig[k-1]
        sig_old, sig = sig, newsig
    return alpha, beta

def chain_g(alpha, beta):
    # a_n = beta_n/(alpha_{n-1} alpha_n), n>=1 ; g_0=0, g_n=a_n/(1-g_{n-1})
    M = len(alpha)
    a = [None]*M; g = [mp.mpf(0)]*M
    for n in range(1, M):
        a[n] = beta[n]/(alpha[n-1]*alpha[n])
        g[n] = a[n]/(1 - g[n-1])
    return a, g

def run(label, xs, ws, M):
    L = 2*M
    m = [sum(w*x**l for x, w in zip(xs, ws)) for l in range(L)]
    alpha, beta = cheb(m, M)
    a, g = chain_g(alpha, beta)
    print("\n[%s]" % label)
    for n in range(1, M):
        gn = g[n]
        realish = abs(mp.im(gn)) < mp.mpf(10)**-18
        flag = "" if (realish and 0 <= mp.re(gn) < 1) else ("  <-- EXITS [0,1)" if realish else "  <-- COMPLEX (FE broken)")
        print("  n=%2d  a_n=%s  g_n=%s%s" % (n, mp.nstr(a[n],8), mp.nstr(gn,8), flag))

# --- sanity check: atoms of a positive measure on [0,1] (should give g_n in [0,1), a_n->1/4) ---
xs0 = [mp.mpf(j)/20 for j in range(1,20)]; ws0 = [mp.mpf(1)]*len(xs0)
run("SANITY uniform-grid (0,1) positive", xs0, ws0, 9)

# --- zeros ---
N = 80
print("\ncomputing %d zeta zeros (dps=50)..." % N, flush=True)
gam = [mp.im(mp.zetazero(n)) for n in range(1, N+1)]
xs = [1/g**2 for g in gam]; ws = [mp.mpf(2)]*N   # weight 2 for +/- gamma pair
run("RH-SIDE (real gamma)", xs, ws, 9)

# --- OFF-LINE separator: move zero #1 off the line by delta=0.2 -> u = gamma_1 - i*delta, x complex ---
delta = mp.mpf('0.2')
xs_off = list(xs)
u1 = gam[0] - 1j*delta
xs_off[0] = 1/u1**2
run("OFF-LINE (zero #1 moved by delta=0.2)", xs_off, ws, 9)

# --- OFF-LINE SYMMETRIC (FE-respecting): zero #1 -> quadruple {+-gamma_1 +- i*beta}; moments STAY REAL ---
# this is the genuine separator: real moments, non-positive measure -> g_n (real) must EXIT [0,1) at finite n.
beta = mp.mpf('0.2')
us = [gam[0]-1j*beta, gam[0]+1j*beta, -gam[0]-1j*beta, -gam[0]+1j*beta]
xs_sym = [1/u**2 for u in us] + xs[1:]
ws_sym = [mp.mpf(1)]*4 + ws[1:]
run("OFF-LINE SYMMETRIC quadruple (FE-respecting, beta=0.2)", xs_sym, ws_sym, 9)

# stronger off-line: beta=2.0 (deeper off the line)
beta2 = mp.mpf('2.0')
us2 = [gam[0]-1j*beta2, gam[0]+1j*beta2, -gam[0]-1j*beta2, -gam[0]+1j*beta2]
xs_sym2 = [1/u**2 for u in us2] + xs[1:]
run("OFF-LINE SYMMETRIC quadruple (beta=2.0, deeper)", xs_sym2, ws_sym, 9)

print("\nDONE", flush=True)

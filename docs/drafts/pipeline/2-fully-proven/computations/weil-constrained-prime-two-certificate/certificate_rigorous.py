#!/usr/bin/env python3
"""certificate_rigorous.py -- P2 certificate with explicit error control (mpmath, 25 digits).

Setting.  a = S/2, V0 = {f in L^2[-a,a] : int e^{+-x/2} f = 0}.  On V0 the restricted Weil form is the
Fourier multiplier
    Q(f) = (1/2pi) int |fhat|^2 m(xi) dxi,   m(xi) = A(S) + Lambda_S(xi) - c_p cos(xi log 2),
    Lambda_S(xi) = int_0^S K+(u)(1 - cos u xi) du,  K+(u) = 2 e^{-u/2}/(1-e^{-2u}) = 2 sum_m e^{-alpha_m u},
    alpha_m = 2m+1/2,  A(S) = -gamma - log pi - log(1-e^{-2S}) - J(S),
    J(S) = 2 sum_m [(1-e^{-alpha_m S})/alpha_m - (1-e^{-beta_m S})/beta_m],  beta_m = 2m+2,
    c_p = sqrt2 log2 if log2 < S < log3 (prime 2, k=1 term), else 0.
Every series is evaluated with a proven tail bound (lower bounds where a lower bound is what the
certificate consumes).  Band Grams use Gauss-Legendre rules (48 nodes on width-w bands, cross-checked
against 96 nodes).  The finite constrained eigenvalue is bounded below by the penalty eigenvalue
lambda_min(M + t C^T C) <= lambda_min(M|V0) (valid for every t >= 0).

Certificate (f in V0 smooth, supported in (-a,a); f = f_L + f_H, f_L = Legendre projection deg < N):
  Q(f) >= [x y] Omega [x y]^T,  x = |f_L|, y = |f_H|, with
  Omega11 = lambda_L (penalised constrained min of the staircase block),
  Omega12 = -(lambda_L^+ eta + c_max eta (1+eta) + D sqrt(M_low)),
  Omega22 = c_last - (c_last - c_min)^+ M_low - c_max (eta^2 + 2 eta),
  M_low = 2 a^{2N+1} Xi^{2N+1} / (pi (N!)^2 (2N+1)^2)      (Taylor localisation of f_H below Xi),
  eta   = sqrt2 eps_N / sqrt(sigma_min),  eps_N = e^{a/2} 2^{-N}/N! sqrt(2 a^{2N+1}/(2N+1))
          (f_L is only eps_N-close to V0), sigma_min >= 2 sinh a - 2a - 2 eps_N^2,
  D = max_b |c_b - c_last|,  c_max = sup |m_stair|.
Ground energy on V0 >= lambda_min(Omega)."""
import sys, json, math
from mpmath import mp, mpf, exp, log, cos, sin, sqrt, pi, euler, besselj, besseli, digamma, matrix, eigsy, factorial, ci as mpci
from mpmath.calculus.quadrature import GaussLegendre
from multiprocessing import Pool

DPS = 25
import os
WIDTH = os.environ.get("WIDTH", "0.05")
mp.dps = DPS
LOG2 = log(mpf(2)); LOG3 = log(mpf(3))

def von_mangoldt(n):
    for p in range(2, n+1):
        if n % p == 0:
            k = n; 
            while k % p == 0: k //= p
            return log(mpf(p)) if k == 1 else mpf(0)
    return mpf(0)

def prime_terms(S):
    """[(coefficient 2Λ(n)/√n, log n)] for every n >= 2 with log n < S"""
    out = []
    n = 2
    while log(mpf(n)) < S:
        L = von_mangoldt(n)
        if L != 0: out.append((2*L/sqrt(mpf(n)), log(mpf(n))))
        n += 1
    return out

def prime_multiplier(terms, xi):
    return sum(c*cos(xi*u) for (c, u) in terms) if terms else mpf(0)

def alpha(m): return 2*m + mpf(1)/2
def beta(m): return 2*m + 2

def J_of(S, M=300):
    head = mpf(0)
    for m in range(M):
        head += (1-exp(-alpha(m)*S))/alpha(m) - (1-exp(-beta(m)*S))/beta(m)
    tail_exact = (digamma(M+1) - digamma(M+mpf(1)/4))/2      # sum_{m>=M} (1/alpha_m - 1/beta_m)
    E = exp(-alpha(M)*S)/(alpha(M)*(1-exp(-2*S)))            # |sum_{m>=M} e^{-alpha S}/alpha| <= E, same for beta
    return 2*(head + tail_exact), 2*E                          # J and an absolute error bound

def A_of(S):
    J, dJ = J_of(S)
    return -euler - log(pi) - log(1-exp(-2*S)) - J, dJ          # A(S) in [A - dJ, A + dJ]

def Lam_lower(S, xi, M=400):
    """rigorous lower bound (partial sum of a nonnegative series); loss <= xi^2/(2 (2M-3/2)^2)"""
    s = mpf(0); cS = cos(S*xi); sS = sin(S*xi); x2 = xi*xi
    for m in range(M):
        al = alpha(m); e = exp(-al*S)
        s += (1-e)/al - (al - e*(al*cS - xi*sS))/(al*al + x2)
    return 2*s

def lipschitz(S, M=400):
    """sup |Lambda_S'| <= int_0^S u K+(u) du <= 2 sum_{m<M} [1-e^{-aS}(1+aS)]/a^2 + 1/(2M-3/2)"""
    s = mpf(0)
    for m in range(M):
        al = alpha(m); s += (1 - exp(-al*S)*(1+al*S))/(al*al)
    return 2*s + mpf(1)/(2*M - mpf(3)/2)

def far_tail_lower(S, A, xi):
    """for all xi' >= xi:  m_S(xi') >= A + gamma + log(S xi) - 2/(S xi) + S/2 - 1/(2 xi) - S^2/4 - S/(2 xi) - 1/xi^2,
       monotone increasing in xi.  From 1/(1-e^{-2u}) >= 1/(2u) + 1/2 and e^{-u/2} >= 1 - u/2:
       K+(u) >= 1/u + 1/2 - u/2;  int_0^S (1-cos u xi)/u du = Cin(S xi) >= gamma + log(S xi) - 2/(S xi)
       (|Ci(x)| <= 2/x);  int_0^S (1-cos u xi) du = S - sin(S xi)/xi >= S - 1/xi;
       int_0^S u (1-cos u xi) du = S^2/2 - S sin(S xi)/xi - (cos(S xi)-1)/xi^2 <= S^2/2 + S/xi + 2/xi^2."""
    return A + euler + log(S*xi) - 2/(S*xi) + S/2 - 1/(2*xi) - S*S/4 - S/(2*xi) - 1/(xi*xi)

def sph_j(n, z):
    return sqrt(pi/(2*z))*besselj(n + mpf(1)/2, z)

def sph_i(n, z):
    return sqrt(pi/(2*z))*besseli(n + mpf(1)/2, z)

def band_gram_worker(args):
    S, N, lo, hi, degree, A, cp = args
    mp.dps = DPS
    S = mpf(S); a = S/2; A = mpf(A); terms = prime_terms(S)
    gl = GaussLegendre(mp)
    nodes = gl.get_nodes(mpf(lo), mpf(hi), degree, mp.prec)
    J = [[sph_j(n, a*x) for (x, w) in nodes] for n in range(N)]
    W = [w for (x, w) in nodes]
    Mv = [A + Lam_lower(S, x) - prime_multiplier(terms, x) for (x, w) in nodes]
    G = [[mpf(0)]*N for _ in range(N)]; Gm = [[mpf(0)]*N for _ in range(N)]
    for n in range(N):
        for k in range(n, N):
            if (k-n) % 2: continue
            ph = (-1)**((k-n)//2)
            f = (2*a)*sqrt(mpf((2*n+1)*(2*k+1)))/pi*ph
            v = sum(W[i]*J[n][i]*J[k][i] for i in range(len(W)))
            vm = sum(W[i]*Mv[i]*J[n][i]*J[k][i] for i in range(len(W)))
            G[n][k] = G[k][n] = v*f; Gm[n][k] = Gm[k][n] = vm*f
    return [[str(x) for x in row] for row in G], [[str(x) for x in row] for row in Gm]

def band_minimum(S, A, cp, L, lo, hi, delta):
    """min of m on [lo,hi] via a grid of spacing <= delta and the Lipschitz bound L (of the full m)"""
    terms = prime_terms(S)
    npts = int(math.ceil((hi-lo)/delta)) + 1
    step = (mpf(hi)-mpf(lo))/(npts-1)
    best = None
    for i in range(npts):
        xi = mpf(lo) + i*step
        v = A + Lam_lower(S, xi) - prime_multiplier(terms, xi)
        if best is None or v < best: best = v
    return best - L*step/2

def run(S, Xi=24.0, Xi2=80.0, width=0.25, delta=0.01, degree=5, procs=32):
    S = mpf(S); a = S/2
    terms = prime_terms(S)
    cp = sum(c for (c, u) in terms) if terms else mpf(0)      # total prime amplitude (bounds the prime multiplier)
    A, dA = A_of(S)
    A = A - dA                                               # lower value of A (certificate consumes a lower bound)
    L = lipschitz(S) + (sum(c*u for (c, u) in terms) if terms else mpf(0))   # Lipschitz constant of m
    N = int(math.ceil(3.3*float(a)*Xi)) + 1
    nb = int(round(Xi/width))
    edges = [mpf(width)*i for i in range(nb+1)]
    cs = [band_minimum(S, A, cp, L, edges[i], edges[i+1], delta) for i in range(nb)]
    # last band [Xi, inf): grid on [Xi, Xi2] plus the analytic far tail (which is monotone, so its value at Xi2 bounds beyond)
    c_grid = band_minimum(S, A, cp, L, mpf(Xi), mpf(Xi2), delta*5)
    c_far = far_tail_lower(S, A, mpf(Xi2)) - cp
    c_last = min(c_grid, c_far)
    # band Grams in parallel
    with Pool(procs) as pool:
        res = pool.map(band_gram_worker, [(str(S), N, str(edges[i]), str(edges[i+1]), degree, str(A), str(cp)) for i in range(nb)])
    grams = [r[0] for r in res]; gramsm = [r[1] for r in res]
    # cross-check one band at higher degree
    chk = band_gram_worker((str(S), N, str(edges[nb//2]), str(edges[nb//2+1]), degree+1, str(A), str(cp)))
    gl_err = max(abs(mpf(grams[nb//2][n][k]) - mpf(chk[0][n][k])) for n in range(N) for k in range(N))
    gl_err_m = max(abs(mpf(gramsm[nb//2][n][k]) - mpf(chk[1][n][k])) for n in range(N) for k in range(N))
    Bsum = matrix(N, N); Mst = matrix(N, N); Mex = matrix(N, N)
    for b in range(nb):
        for n in range(N):
            for k in range(N):
                g = mpf(grams[b][n][k]); Bsum[n,k] += g; Mst[n,k] += cs[b]*g; Mex[n,k] += mpf(gramsm[b][n][k])
    for n in range(N):
        for k in range(N):
            Mst[n,k] += c_last*((1 if n == k else 0) - Bsum[n,k]); Mex[n,k] += c_last*((1 if n == k else 0) - Bsum[n,k])
    # constraint vectors <e^{+-x/2}, p_n> = sqrt((2n+1)/(2a)) * a * 2 i_n(a/2) * (+-1)^n
    vp = [sqrt(mpf(2*n+1)/(2*a))*a*2*sph_i(n, a/2) for n in range(N)]
    vm = [vp[n]*((-1)**n) for n in range(N)]
    c_max = max([abs(c) for c in cs] + [abs(c_last)])
    c_min = min(cs + [c_last])
    t = mpf(10)**6*c_max
    Mpen = matrix(N, N)
    for n in range(N):
        for k in range(N):
            Mpen[n,k] = Mst[n,k] + t*(vp[n]*vp[k] + vm[n]*vm[k])
    E = eigsy(Mpen, eigvals_only=True)
    lam_L = min(E)
    Mpex = matrix(N, N)
    for n in range(N):
        for k in range(N):
            Mpex[n,k] = Mex[n,k] + t*(vp[n]*vp[k] + vm[n]*vm[k])
    lam_exact = min(eigsy(Mpex, eigvals_only=True))
    # unpenalised value via an orthonormal basis of the nullspace (for comparison only)
    # Gram-Schmidt: complement of span(vp, vm)
    def dot(u, v): return sum(u[i]*v[i] for i in range(N))
    q1 = [x/sqrt(dot(vp, vp)) for x in vp]
    r = [vm[i] - dot(vm, q1)*q1[i] for i in range(N)]; q2 = [x/sqrt(dot(r, r)) for x in r]
    P = matrix(N, N)
    for n in range(N):
        for k in range(N):
            P[n,k] = (1 if n == k else 0) - q1[n]*q1[k] - q2[n]*q2[k]
    Mc = P*Mst*P + mpf(1000)*c_max*(mp.eye(N) - P)
    lam_c = min(eigsy(Mc, eigvals_only=True))
    # assembly constants
    Nf = factorial(N)
    M_low = 2*a**(2*N+1)*mpf(Xi)**(2*N+1)/(pi*Nf**2*(2*N+1)**2)
    eps = exp(a/2)*mpf(2)**(-N)/Nf*sqrt(2*a**(2*N+1)/(2*N+1))
    sigma_min = 2*mp.sinh(a) - 2*a - 2*eps**2
    eta = sqrt(mpf(2))*eps/sqrt(sigma_min)
    D = max(abs(c - c_last) for c in cs)
    O11 = lam_L
    O12 = -(max(lam_L, 0)*eta + c_max*eta*(1+eta) + D*sqrt(M_low))
    O22 = c_last - max(c_last - c_min, 0)*M_low - c_max*(eta**2 + 2*eta)
    tr = O11 + O22; det = O11*O22 - O12**2
    lam_min = (tr - sqrt(tr*tr - 4*det))/2
    out = dict(S=float(S), a=float(a), prime_terms=[(float(c), float(u)) for (c, u) in terms], prime_amplitude=float(cp), A=float(A), dA=float(dA), L=float(L), N=N, Xi=Xi, Xi2=Xi2,
               width=width, delta=delta, nbands=nb, c_first=float(cs[0]), c_min=float(c_min), c_last=float(c_last),
               c_grid=float(c_grid), c_far=float(c_far), c_max=float(c_max), D=float(D), gl_cross_check=float(gl_err), gl_cross_check_m=float(gl_err_m), lam_exact_block=float(lam_exact),
               lam_L_penalised=float(lam_L), lam_L_nullspace=float(lam_c), M_low=float(M_low), eps=float(eps),
               eta=float(eta), Omega=[float(O11), float(O12), float(O22)], certified_ground_energy=float(lam_min),
               band_minima=[float(c) for c in cs])
    print(json.dumps(out), flush=True)
    return out

if __name__ == "__main__":
    Ss = sys.argv[1:] or ["0.6931471805599453"]
    res = []
    for S in Ss:
        if S == "log2": S = str(LOG2)
        res.append(run(S, width=float(WIDTH), delta=float(WIDTH)/10))
    json.dump(res, open("certificate_rigorous_%s.json" % ("_".join(x[:5] for x in Ss)), "w"), indent=1)

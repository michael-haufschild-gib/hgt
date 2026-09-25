#!/usr/bin/env python3
"""certificate_upper.py -- rigorous UPPER bound of the constrained ground energy mu_0(S).

Rayleigh quotient of an explicit test function f = sum c_n p_n (normalised Legendre, degree < N) that
lies in V0 (both exponential moments zero) and vanishes at both endpoints, so that
|fhat(xi)| <= W / xi^2 with W = |f'(a)| + |f'(-a)| + int |f''| (two integrations by parts).
  Q(f) = (1/2pi) int |fhat|^2 m(xi) dxi  <=  [exact-multiplier Gram on [0, Xi2]] + W^2 * int_{Xi2}^inf m_up(xi)/xi^4 dxi / pi,
  m_up(xi) = A + gamma + log(S xi) + 2/(S xi) + 2S + 2/xi   (from K+ <= 1/h + 2 and Cin(x) <= gamma + log x + 2/x),
  Lambda upper bound = 2 sum_{m<M} T_m + xi^2/(2(2M-3/2)^2)   (M = 4000 on [0, Xi2 = 200]).
The minimiser is taken from the penalised exact-multiplier block (4 constraints), which is only a choice of
test function; the bound is rigorous for that function."""
import sys, json, math, os
from mpmath import mp, mpf, exp, log, cos, sin, sqrt, pi, euler, besselj, besseli, matrix, eigsy, legendre, diff
from mpmath.calculus.quadrature import GaussLegendre
from multiprocessing import Pool
import certificate_rigorous as C

DPS = C.DPS
mp.dps = DPS

def band_gram_upper_worker(args):
    S, N, lo, hi, degree, A, M = args
    mp.dps = DPS
    S = mpf(S); a = S/2; A = mpf(A); terms = C.prime_terms(S)
    gl = GaussLegendre(mp)
    nodes = gl.get_nodes(mpf(lo), mpf(hi), degree, mp.prec)
    J = [[C.sph_j(n, a*x) for (x, w) in nodes] for n in range(N)]
    W = [w for (x, w) in nodes]
    Mv = [A + C.Lam_lower(S, x, M) + x*x/(2*(2*M - mpf(3)/2)**2) - C.prime_multiplier(terms, x) for (x, w) in nodes]
    Gm = [[mpf(0)]*N for _ in range(N)]
    for n in range(N):
        for k in range(n, N):
            if (k-n) % 2: continue
            ph = (-1)**((k-n)//2)
            f = (2*a)*sqrt(mpf((2*n+1)*(2*k+1)))/pi*ph
            vm = sum(W[i]*Mv[i]*J[n][i]*J[k][i] for i in range(len(W)))
            Gm[n][k] = Gm[k][n] = vm*f
    return [[str(x) for x in row] for row in Gm]

def run(S, Xi2=1000.0, width=0.5, degree=5, M=2000, procs=16):
    S = mpf(S); a = S/2
    A, dA = C.A_of(S); A = A + dA                       # upper value of A
    N = int(math.ceil(3.3*float(a)*24.0)) + 1
    nb = int(round(Xi2/width)); edges = [mpf(width)*i for i in range(nb+1)]
    with Pool(procs) as pool:
        grams = pool.map(band_gram_upper_worker, [(str(S), N, str(edges[i]), str(edges[i+1]), degree, str(A), M) for i in range(nb)])
    Mex = matrix(N, N)
    for b in range(nb):
        for n in range(N):
            for k in range(N):
                Mex[n,k] += mpf(grams[b][n][k])
    # constraints: exponential moments and endpoint values
    vp = [sqrt(mpf(2*n+1)/(2*a))*a*2*C.sph_i(n, a/2) for n in range(N)]
    vm = [vp[n]*((-1)**n) for n in range(N)]
    ep = [sqrt(mpf(2*n+1)/(2*a)) for n in range(N)]                 # p_n(a)  (P_n(1) = 1)
    em = [ep[n]*((-1)**n) for n in range(N)]                         # p_n(-a)
    cons = [vp, vm, ep, em]
    t = mpf(10)**8
    Mpen = matrix(N, N)
    for n in range(N):
        for k in range(N):
            Mpen[n,k] = Mex[n,k] + t*sum(c[n]*c[k] for c in cons)
    # derivative Gram D'[n,k] = int p_n' p_k' (exact for polynomials via 8x96-node Gauss-Legendre)
    gl0 = GaussLegendre(mp)
    def pderiv(n, x): return sqrt(mpf(2*n+1)/(2*a))*diff(lambda y: legendre(n, y/a), x, 1)
    Dp = matrix(N, N)
    nodes_all = []
    for s_ in range(8):
        lo_ = -a + 2*a*s_/8; hi_ = -a + 2*a*(s_+1)/8
        nodes_all += gl0.get_nodes(lo_, hi_, 6, mp.prec)
    PD = [[pderiv(n, x) for (x, w) in nodes_all] for n in range(N)]
    for n in range(N):
        for k in range(n, N):
            v_ = sum(w*PD[n][i]*PD[k][i] for i, (x, w) in enumerate(nodes_all))
            Dp[n,k] = Dp[k,n] = v_
    X = mpf(Xi2); cpp = sum(c for (c, u) in C.prime_terms(S)) if C.prime_terms(S) else mpf(0)
    # sup_{xi >= Xi2} m_up(xi)/xi^2 : m_up increasing slowly, m_up/xi^2 decreasing for xi >= Xi2 (log xi/xi^2 decreasing past e^{1/2})
    tau = (A + euler + log(S*X) + 2/(S*X) + 2*S + 2/X + cpp)/X**2
    for n in range(N):
        for k in range(N):
            Mpen[n,k] += tau*Dp[n,k]
    E, V = eigsy(Mpen)
    j = min(range(N), key=lambda i: E[i])
    v = [V[i, j] for i in range(N)]
    # project exactly onto the constraint nullspace (Gram-Schmidt on the 4 constraint vectors)
    def dot(x, y): return sum(x[i]*y[i] for i in range(N))
    Q = []
    for c in cons:
        r = list(c)
        for q in Q:
            d = dot(r, q); r = [r[i] - d*q[i] for i in range(N)]
        nr = sqrt(dot(r, r)); Q.append([x/nr for x in r])
    for q in Q:
        d = dot(v, q); v = [v[i] - d*q[i] for i in range(N)]
    nv2 = dot(v, v)
    resid = [abs(dot(v, c)) for c in cons]
    # f(x) = sum v_n sqrt((2n+1)/(2a)) P_n(x/a); f' and f'' via Legendre derivatives
    def fval(x, d=0):
        return sum(v[n]*sqrt(mpf(2*n+1)/(2*a))*diff(lambda y: legendre(n, y/a), x, d) for n in range(N))
    fpa = abs(fval(a, 1)); fpma = abs(fval(-a, 1))
    # int |f''| over [-a,a] by Gauss-Legendre with 96 nodes on 8 subintervals (f'' is a polynomial of degree N-3)
    gl = GaussLegendre(mp)
    intf2 = mpf(0)
    for s in range(8):
        lo = -a + 2*a*s/8; hi = -a + 2*a*(s+1)/8
        for (x, w) in gl.get_nodes(lo, hi, 6, mp.prec):
            intf2 += w*abs(fval(x, 2))
    Wtv = fpa + fpma + intf2
    # tail: (1/pi) int_{Xi2}^inf m_up(xi) W^2/xi^4 dxi, m_up increasing bound -> use closed form pieces
    X = mpf(Xi2)
    cp = sum(c for (c, u) in C.prime_terms(S)) if C.prime_terms(S) else mpf(0)
    # int_X^inf log(S xi)/xi^4 = (log(S X) + 1/3)/(3 X^3);  int_X^inf 1/xi^4 = 1/(3X^3); int 1/xi^5 = 1/(4X^4)
    tail = (Wtv**2/pi)*((A + euler + 2*S + cp)/(3*X**3) + (log(S*X) + mpf(1)/3)/(3*X**3) + (2/S + 2)/(4*X**4))
    Qv = sum(v[n]*Mex[n,k]*v[k] for n in range(N) for k in range(N))
    Dv = sum(v[n]*Dp[n,k]*v[k] for n in range(N) for k in range(N))
    upper = (Qv + tau*Dv)/nv2
    out = dict(S=float(S), N=N, Xi2=Xi2, width=width, M=M, constraint_residuals=[float(r) for r in resid],
               endpoint_derivatives=[float(fpa), float(fpma)], int_abs_f2=float(intf2), W=float(Wtv), tail=float(tail),
               block_quotient=float(Qv/nv2), tau=float(tau), deriv_energy=float(Dv/nv2), upper_bound=float(upper), coeffs=[float(x/sqrt(nv2)) for x in v])
    print(json.dumps(out), flush=True)
    return out

if __name__ == "__main__":
    for S in sys.argv[1:]:
        run(mpf(S) if S != "log2" else C.LOG2)

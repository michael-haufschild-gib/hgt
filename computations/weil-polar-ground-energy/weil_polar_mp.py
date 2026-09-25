#!/usr/bin/env python3
"""
High-precision (mpmath) Galerkin computation of the pole-vanishing ground energy of the
restricted Weil form.  Same conventions as weil_polar_galerkin.py:

  Q(f) = 2 c_+ c_-  -  2 sum_n Lambda(n) n^{-1/2} g(log n)  +  Arch(f),
  Arch(f) = (-gamma - log pi) g(0) + 2 int_0^inf [g(0) e^{-2u} - g(u) e^{-u/2}]/(1 - e^{-2u}) du,

on the orthonormal Legendre basis of L^2(-a, a).  All quadratures are Gauss-Legendre in mpmath
(exact for the polynomial overlaps, spectrally convergent for the analytic u-integrand).

Outputs, per aperture a and basis size N:
  mu_full   lowest eigenvalue of Q on L^2(-a,a)
  mu0_full  lowest eigenvalue of Q on V0 = {c_+ = c_- = 0}
  mu0_arch  lowest eigenvalue of Arch on V0
  mu0_le_P  lowest eigenvalue of Arch - (primes n <= P) on V0
"""
import sys, json, math, time
from mpmath import mp, mpf, mpmathify, euler, pi, log, exp, sqrt, matrix, eigsy, expm1
from mpmath.calculus.quadrature import GaussLegendre
from multiprocessing import Pool


def gl_nodes(deg):
    """Gauss-Legendre nodes/weights on [-1,1] at current precision; 3*2^(deg-1) points."""
    gl = GaussLegendre(mp)
    return gl.calc_nodes(deg, mp.prec)


def legendre_vec(t, N):
    """P_0(t) .. P_{N-1}(t) by the three-term recurrence."""
    out = [mpf(1)] * N
    if N > 1:
        out[1] = t
    for k in range(1, N - 1):
        out[k + 1] = ((2 * k + 1) * t * out[k] - k * out[k - 1]) / (k + 1)
    return out


def vonmangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            q = n
            while q % p == 0:
                q //= p
            return log(p) if q == 1 else mpf(0)
    return mpf(0)


class WeilMP:
    def __init__(self, a, N, deg_x=5, deg_u=6):
        self.a = mpmathify(a)
        self.N = N
        self.S = 2 * self.a
        self.norm = [sqrt(mpf(2 * k + 1) / (2 * self.a)) for k in range(N)]
        self.nodes_x = gl_nodes(deg_x)     # 48 nodes: exact for polynomial degree <= 95
        self.nodes_u = gl_nodes(deg_u)     # 96 nodes per piece

    def basis(self, x):
        if abs(x) > self.a:
            return [mpf(0)] * self.N
        P = legendre_vec(x / self.a, self.N)
        return [self.norm[k] * P[k] for k in range(self.N)]

    def overlap_sym(self, u):
        """(G(u) + G(u)^T)/2 with G(u)_{jk} = int P~_j(x) P~_k(x-u) dx, 0 <= u < S."""
        N = self.N
        G = matrix(N, N)
        if u >= self.S:
            return G
        lo, hi = u - self.a, self.a
        half = (hi - lo) / 2
        mid = (hi + lo) / 2
        for t, w in self.nodes_x:
            x = half * t + mid
            ww = half * w
            v1 = self.basis(x)
            v2 = self.basis(x - u)
            for j in range(N):
                vj = ww * v1[j]
                if vj == 0:
                    continue
                for k in range(N):
                    G[j, k] += vj * v2[k]
        for j in range(N):
            for k in range(j + 1, N):
                s = (G[j, k] + G[k, j]) / 2
                G[j, k] = s
                G[k, j] = s
        return G

    def pole_vectors(self):
        cp = [mpf(0)] * self.N
        cm = [mpf(0)] * self.N
        for t, w in self.nodes_x:
            x = self.a * t
            ww = self.a * w
            v = self.basis(x)
            ep, em = exp(x / 2), exp(-x / 2)
            for j in range(self.N):
                cp[j] += ww * ep * v[j]
                cm[j] += ww * em * v[j]
        return cp, cm

    def arch_matrix(self, pieces=None):
        N, S = self.N, self.S
        I = mp.eye(N)
        A = (-euler - log(pi)) * I
        if pieces is None:
            pieces = [mpf(0), min(mpf('0.125'), S / 4), min(mpf('0.5'), S / 2), S]
            pieces = sorted(set(pieces))
        acc = matrix(N, N)
        for lo, hi in zip(pieces[:-1], pieces[1:]):
            half = (hi - lo) / 2
            mid = (hi + lo) / 2
            for t, w in self.nodes_u:
                u = half * t + mid
                ww = half * w
                den = -expm1(-2 * u)
                Gu = self.overlap_sym(u)
                e2 = exp(-2 * u) / den
                eh = exp(-u / 2) / den
                for j in range(N):
                    for k in range(N):
                        acc[j, k] += ww * ((e2 if j == k else 0) - Gu[j, k] * eh)
        A += 2 * acc
        A += (-log(-expm1(-2 * S))) * I
        return A

    def prime_matrix(self, pmax=None):
        N, S = self.N, self.S
        P = matrix(N, N)
        nmax = int(math.floor(float(exp(S))))
        for n in range(2, nmax + 1):
            lam = vonmangoldt(n)
            if lam == 0 or (pmax is not None and n > pmax):
                continue
            ln = log(n)
            if ln >= S:
                continue
            G = self.overlap_sym(ln)
            c = 2 * lam / sqrt(n)
            for j in range(N):
                for k in range(N):
                    P[j, k] += c * G[j, k]
        return P

    @staticmethod
    def lowest(M):
        E = eigsy(M, eigvals_only=True)
        return min(E)

    def constrained_projector(self):
        cp, cm = self.pole_vectors()
        # Gram-Schmidt on the two constraint vectors
        q1 = matrix(cp)
        q1 = q1 / sqrt(sum(x * x for x in q1))
        q2 = matrix(cm)
        q2 = q2 - (sum(q1[i] * q2[i] for i in range(self.N))) * q1
        q2 = q2 / sqrt(sum(x * x for x in q2))
        P = mp.eye(self.N) - q1 * q1.T - q2 * q2.T
        return P, cp, cm

    def lowest_constrained(self, Q, P, shift=mpf(1000)):
        M = P * Q * P + shift * (mp.eye(self.N) - P)
        return self.lowest(M)


def compute(args):
    a, N, dps, pmax_list = args
    mp.dps = dps
    t0 = time.time()
    W = WeilMP(a, N)
    A = W.arch_matrix()
    P, cp, cm = W.constrained_projector()
    Pole = matrix(N, N)
    for j in range(N):
        for k in range(N):
            Pole[j, k] = cp[j] * cm[k] + cm[j] * cp[k]
    Pr = W.prime_matrix()
    Q = A + Pole - Pr
    out = {"a": float(a), "N": N, "dps": dps,
           "mu_full": mp.nstr(W.lowest(Q), 25),
           "mu0_full": mp.nstr(W.lowest_constrained(Q, P), 25),
           "mu0_arch": mp.nstr(W.lowest_constrained(A, P), 25)}
    for pm in pmax_list:
        out[f"mu0_le_{pm}"] = mp.nstr(W.lowest_constrained(A - W.prime_matrix(pmax=pm), P), 25)
    out["seconds"] = round(time.time() - t0, 1)
    print(json.dumps(out), flush=True)
    return out


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "probe":
        jobs = [(a, N, 60, (2, 3, 5)) for a in ("0.35", "0.5", "0.7", "0.9", "1.1", "1.3", "1.5")
                for N in (32, 44)]
    elif mode == "hp":
        # high-precision scan of the pole-vanishing full form through the first prime thresholds
        apts = [f"{x/100:.2f}" for x in range(30, 161, 5)]
        jobs = [(a, N, 80, (2, 3, 5, 7)) for a in apts for N in (40, 56)]
    elif mode == "sqrt2":
        jobs = [(a, N, 60, (2,)) for a in ("0.3465735902799726",) for N in (24, 32, 40, 48, 56, 64)]
    else:
        raise SystemExit("mode?")
    with Pool(min(16, len(jobs))) as pool:
        res = pool.map(compute, jobs)
    with open(f"mp_{mode}.json", "w") as fh:
        json.dump(res, fh, indent=1)

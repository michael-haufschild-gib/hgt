#!/usr/bin/env python3
"""
Galerkin computation of the restricted Weil quadratic form on L^2(-a, a) and of its
ground energies, with and without the two pole constraints, with and without the primes.

Conventions (additive variable x = log u, real test f supported in [-a, a], S = 2a):

  g(x)      = autocorrelation  int f(y) f(y - x) dy            (even, supported in [-S, S])
  c_pm      = int e^{pm x/2} f(x) dx                              (the two pole coefficients)
  Pole(f)   = 2 c_+ c_-
  Prime(f)  = 2 sum_{n >= 2} Lambda(n) n^{-1/2} g(log n)          (only n < e^S contribute)
  Arch(f)   = (-gamma - log pi) g(0)
              + 2 int_0^inf [ g(0) e^{-2u} - g(u) e^{-u/2} ] / (1 - e^{-2u}) du
            = int_R 2 theta'(2 pi xi) |fhat(xi)|^2 dxi ,  2 theta'(t) = Re psi(1/4 + i t/2) - log pi
  Q(f)      = Pole(f) - Prime(f) + Arch(f)

Weil's explicit formula gives Q(f) = sum_rho F(rho) F(1 - rho) with F(s) = int f(x) e^{(s-1/2) x} dx,
so RH  <=>  Q(f) >= 0 for all f and all apertures a.

Ground energies computed (lowest eigenvalue of the Galerkin matrix on an orthonormal Legendre basis):
  mu_full(a)     : Q on all of L^2(-a,a)                        (Suzuki's lowest eigenvalue lambda_a)
  mu0_full(a)    : Q on V0 = {c_+ = c_- = 0}                     (pole-vanishing subspace)
  mu0_arch(a)    : Arch alone on V0                              (no primes)
  mu0_primes<=P  : Arch - (primes with n <= P) on V0             (which primes are needed)

All matrices are assembled from exact Gauss-Legendre quadrature of polynomial overlaps and a
smooth one-dimensional u-integral.  A Fourier-side cross-check of the archimedean matrix is
included (integration of 2 theta'(2 pi xi) against products of spherical Bessel functions).
"""
import json, math, sys, time
import numpy as np
from numpy.polynomial.legendre import leggauss, legvander
from scipy.special import spherical_jn, psi as digamma
from mpmath import mp, mpf, euler, pi as mppi, digamma as mpdigamma, quad as mpquad, exp as mpexp

EULER = float(euler)
LOGPI = math.log(math.pi)


def vonmangoldt_upto(N):
    """Lambda(n) for n = 0..N (0 for non prime powers)."""
    lam = np.zeros(N + 1)
    for p in range(2, N + 1):
        if all(p % q for q in range(2, int(math.isqrt(p)) + 1)):
            pk = p
            while pk <= N:
                lam[pk] = math.log(p)
                pk *= p
    return lam


class WeilGalerkin:
    def __init__(self, a, N, Mx=None, Mu=(120, 400)):
        self.a = float(a)
        self.N = int(N)                     # basis: orthonormal Legendre P~_0 .. P~_{N-1}
        self.S = 2 * self.a
        self.Mx = Mx or (self.N + 8)
        self.Mu = Mu
        self.norm = np.sqrt((2 * np.arange(self.N) + 1) / (2 * self.a))

    # ---- basis --------------------------------------------------------------------------
    def basis(self, x):
        """Orthonormal Legendre basis on [-a, a]; zero outside.  x: array -> (len(x), N)."""
        x = np.asarray(x, dtype=float)
        inside = np.abs(x) <= self.a * (1 + 1e-15)
        V = np.zeros((x.size, self.N))
        if inside.any():
            t = np.clip(x[inside] / self.a, -1, 1)
            V[inside] = legvander(t, self.N - 1) * self.norm
        return V

    # ---- overlaps -----------------------------------------------------------------------
    def overlap(self, u):
        """G(u)_{jk} = int P~_j(x) P~_k(x - u) dx  for 0 <= u < S (exact Gauss quadrature)."""
        if u >= self.S:
            return np.zeros((self.N, self.N))
        lo, hi = u - self.a, self.a
        t, w = leggauss(self.Mx)
        x = 0.5 * (hi - lo) * t + 0.5 * (hi + lo)
        w = 0.5 * (hi - lo) * w
        Vx = self.basis(x)
        Vxu = self.basis(x - u)
        return (Vx * w[:, None]).T @ Vxu

    def overlap_sym(self, u):
        G = self.overlap(abs(u))
        return 0.5 * (G + G.T)

    # ---- pole vectors -------------------------------------------------------------------
    def pole_vectors(self):
        t, w = leggauss(max(self.Mx, 80))
        x = self.a * t
        w = self.a * w
        V = self.basis(x)
        cp = (V * (w * np.exp(0.5 * x))[:, None]).sum(axis=0)
        cm = (V * (w * np.exp(-0.5 * x))[:, None]).sum(axis=0)
        return cp, cm

    # ---- matrices -----------------------------------------------------------------------
    def prime_matrix(self, pmax=None):
        """2 sum_n Lambda(n) n^{-1/2} G_s(log n), n < e^S (optionally only n <= pmax)."""
        nmax = int(math.floor(math.exp(self.S) - 1e-12))
        lam = vonmangoldt_upto(max(nmax, 2))
        P = np.zeros((self.N, self.N))
        for n in range(2, nmax + 1):
            if lam[n] == 0:
                continue
            if pmax is not None and n > pmax:
                continue
            ln = math.log(n)
            if ln >= self.S:
                continue
            P += 2 * lam[n] / math.sqrt(n) * self.overlap_sym(ln)
        return P

    def arch_matrix(self):
        """Arch_{jk} via the time-domain representation (no Fourier tails)."""
        N, S = self.N, self.S
        I = np.eye(N)
        A = (-EULER - LOGPI) * I
        # 2 int_0^S [I e^{-2u} - G_s(u) e^{-u/2}] / (1 - e^{-2u}) du, split at u0 = min(0.25, S/2)
        u0 = min(0.25, S / 2)
        acc = np.zeros((N, N))
        for (lo, hi, M) in ((0.0, u0, self.Mu[0]), (u0, S, self.Mu[1])):
            t, w = leggauss(M)
            u = 0.5 * (hi - lo) * t + 0.5 * (hi + lo)
            w = 0.5 * (hi - lo) * w
            for ui, wi in zip(u, w):
                den = -np.expm1(-2 * ui)          # 1 - e^{-2u}, accurate near 0
                acc += wi * (I * np.exp(-2 * ui) - self.overlap_sym(ui) * np.exp(-0.5 * ui)) / den
        A += 2 * acc
        # tail u > S: g(u) = 0, 2 int_S^inf e^{-2u}/(1-e^{-2u}) du = -log(1 - e^{-2S})
        A += (-np.log(-np.expm1(-2 * S))) * I
        return A

    def arch_matrix_fourier(self, Z=6000.0, nz=600000):
        """Cross-check: Arch_{jk} = 2a sqrt((2j+1)(2k+1)) (-1)^{(j-k)/2} (1/(pi a)) int_0^inf
        2theta'(z/a) j_j(z) j_k(z) dz  (j+k even), with a non-oscillatory tail correction."""
        N, a = self.N, self.a
        z = np.linspace(1e-9, Z, nz)
        th = np.real(digamma(0.25 + 0.5j * (z / a))) - LOGPI          # 2 theta'(z/a)
        J = np.array([spherical_jn(k, z) for k in range(N)])
        A = np.zeros((N, N))
        for j in range(N):
            for k in range(j, N):
                if (j + k) % 2:
                    continue
                val = np.trapz(th * J[j] * J[k], z)
                # non-oscillatory tail: j_j j_k ~ cos((j-k)pi/2)/(2 z^2), 2theta'(z/a) ~ log(z/(2 pi a))
                c = math.cos((j - k) * math.pi / 2) / 2
                tail = c * (math.log(Z / (2 * math.pi * a)) + 1) / Z
                val += tail
                A[j, k] = A[k, j] = (2 * a * math.sqrt((2 * j + 1) * (2 * k + 1))
                                     * (-1) ** ((j - k) // 2) * val / (math.pi * a))
        return A

    # ---- ground energies ---------------------------------------------------------------
    def assemble(self, pmax=None, with_primes=True, with_pole=True):
        A = self.arch_matrix()
        Q = A.copy()
        if with_pole:
            cp, cm = self.pole_vectors()
            Q += np.outer(cp, cm) + np.outer(cm, cp)
        if with_primes:
            Q -= self.prime_matrix(pmax=pmax)
        return Q

    def constrained_basis(self):
        cp, cm = self.pole_vectors()
        C = np.vstack([cp, cm])
        # orthonormal basis of the null space of C
        _, s, Vt = np.linalg.svd(C)
        rank = int((s > 1e-13 * s.max()).sum())
        return Vt[rank:].T          # N x (N - rank)

    @staticmethod
    def lowest(Qm):
        w = np.linalg.eigvalsh(0.5 * (Qm + Qm.T))
        return float(w[0]), float(w[1]) if len(w) > 1 else float('nan')


def mp_check_arch_entry(a, N, j, k, dps=30):
    """High-precision check of one archimedean matrix entry via mpmath (time-domain formula)."""
    mp.dps = dps
    a = mpf(a); S = 2 * a
    from mpmath import legendre, sqrt as msqrt, log as mlog
    nj = msqrt((2 * j + 1) / (2 * a)); nk = msqrt((2 * k + 1) / (2 * a))

    def P(m, x):
        return legendre(m, x / a)

    def g(u):   # symmetrized overlap
        u = abs(u)
        if u >= S:
            return mpf(0)
        f1 = mpquad(lambda x: nj * P(j, x) * nk * P(k, x - u), [u - a, a])
        f2 = mpquad(lambda x: nk * P(k, x) * nj * P(j, x - u), [u - a, a])
        return (f1 + f2) / 2

    g0 = g(0)
    integrand = lambda u: (g0 * mpexp(-2 * u) - g(u) * mpexp(-u / 2)) / (1 - mpexp(-2 * u))
    val = (-euler - mlog(mppi)) * g0 + 2 * mpquad(integrand, [0, S / 8, S / 2, S]) \
        + 2 * g0 * (-mlog(1 - mpexp(-2 * S)) / 2)
    return float(val)


def run_sweep(apertures, Ns, out_json, pmax_list=(2, 3, 5, 7)):
    results = []
    t0 = time.time()
    for a in apertures:
        row = {"a": float(a), "lambda": float(math.exp(a)), "S": float(2 * a), "N": {}}
        for N in Ns:
            W = WeilGalerkin(a, N)
            A = W.arch_matrix()
            cp, cm = W.pole_vectors()
            Pole = np.outer(cp, cm) + np.outer(cm, cp)
            Pr_all = W.prime_matrix()
            Z = W.constrained_basis()
            Qfull = A + Pole - Pr_all
            entry = {
                "mu_full": W.lowest(Qfull)[0],
                "mu0_full": W.lowest(Z.T @ Qfull @ Z)[0],
                "mu0_arch": W.lowest(Z.T @ A @ Z)[0],
                "mu_arch_pole": W.lowest(A + Pole)[0],
                "mu0_second": W.lowest(Z.T @ Qfull @ Z)[1],
            }
            for pm in pmax_list:
                Pr = W.prime_matrix(pmax=pm)
                entry[f"mu0_primes_le_{pm}"] = W.lowest(Z.T @ (A - Pr) @ Z)[0]
            row["N"][str(N)] = entry
        results.append(row)
        print(f"a={a:.4f} lam={math.exp(a):.4f} " +
              " ".join(f"N{N}:mu0_full={row['N'][str(N)]['mu0_full']:+.6e}" for N in Ns) +
              f"  mu0_arch(N{Ns[-1]})={row['N'][str(Ns[-1])]['mu0_arch']:+.6e}"
              f"  mu_full={row['N'][str(Ns[-1])]['mu_full']:+.6e}  [{time.time()-t0:.0f}s]", flush=True)
        with open(out_json, "w") as fh:
            json.dump(results, fh, indent=1)
    return results


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "checks"
    if mode == "checks":
        # 1. Fourier vs time-domain archimedean matrix
        for a in (0.2, 0.3466, 0.6):
            W = WeilGalerkin(a, 8)
            A1 = W.arch_matrix()
            A2 = W.arch_matrix_fourier()
            print(f"a={a}: max|A_time - A_fourier| = {np.abs(A1 - A2).max():.3e}, "
                  f"max|A| = {np.abs(A1).max():.3e}")
            print("  A_time diag  :", np.round(np.diag(A1), 6))
            print("  A_four diag  :", np.round(np.diag(A2), 6))
        # 2. mpmath check of a few entries
        for a in (0.3466,):
            W = WeilGalerkin(a, 12)
            A1 = W.arch_matrix()
            for (j, k) in ((0, 0), (1, 1), (2, 0), (3, 3), (5, 7), (10, 10)):
                v = mp_check_arch_entry(a, 12, j, k)
                print(f"  a={a} entry ({j},{k}): double={A1[j,k]:.12e} mpmath={v:.12e} diff={abs(A1[j,k]-v):.2e}")
        # 3. indicator-function sanity: f = 1 on [-a,a]; g(u) = (2a-|u|)_+
        a = 0.3
        g0 = 2 * a
        f_arch = (-EULER - LOGPI) * g0 + 2 * float(mpquad(lambda u: (g0 * mpexp(-2*u) - max(2*a - u, 0) * mpexp(-u/2)) / (1 - mpexp(-2*u)), [0, 2*a, mp.inf]))
        xi = np.linspace(1e-9, 4000, 4000000)
        fhat2 = (np.sin(2 * np.pi * a * xi) / (np.pi * xi)) ** 2
        th = np.real(digamma(0.25 + 1j * np.pi * xi)) - LOGPI
        f_four = 2 * np.trapz(th * fhat2, xi) + 2 * (math.log(4000 / (2 * math.pi * a)) + 1) / (4000 * 2 * math.pi ** 2 * a ** 2) * 0  # tail negligible here
        print(f"indicator a={a}: Arch(time)={f_arch:.6f}  Arch(fourier, truncated)={f_four:.6f}")
    elif mode == "sweep":
        apertures = [float(x) for x in np.concatenate([
            np.arange(0.05, 0.30, 0.05),
            np.arange(0.30, 0.40, 0.01),      # around log2/2 = 0.3466
            np.arange(0.40, 0.56, 0.02),      # around log3/2 = 0.5493
            np.arange(0.56, 1.00, 0.04),
            np.arange(1.00, 2.01, 0.10)])]
        Ns = [24, 36, 48, 64]
        run_sweep(apertures, Ns, "sweep_results.json")
    elif mode == "fine":
        # fine scan of the archimedean-only V0 ground energy to locate its zero, and of the
        # pole-vanishing full form across the prime thresholds
        apertures = [float(x) for x in np.arange(0.30, 1.60, 0.01)]
        Ns = [48, 64]
        run_sweep(apertures, Ns, "fine_results.json", pmax_list=(2, 3, 5))

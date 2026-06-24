#!/usr/bin/env python3
"""
Tensegrity / universal-rigidity collision with the reciprocal-seam Hankel.
Entropy seed 410091500312701155; domain=tensegrity(x2); method=split.

Question (object-level, testable, with null control):
  Read RH-positivity as prestress-stability of the prime-arch tensegrity.
  An off-line zero = a FLEX (unblocked infinitesimal motion). The "softest mode"
  of the shifted Hankel H_d = [T_{i+j+1}] is the nearest-to-a-flex direction.
  DOES the softest-mode / Jacobi propagation d->d+1 distinguish the genuine zeta
  reciprocal-seam divisor from the RH-empty FID integer divisor?

  T_k        = 2 * sum_{gamma>0} gamma^{-2k}     (zeta reciprocal-seam, Voros)
  T_k^FID    = zeta(2k+1)                        (integer divisor 1/n^2, RH-empty)
  H_d[i,j]   = T_{i+j+1}, i,j=0..d-1             (shifted Hankel "tensegrity stress")

Report, side by side (zeta vs FID): lambda_min(H_d), cond(H_d), Jacobi beta_n,
and the softest-eigenvector overlap between consecutive d (does the flex direction
propagate the same way in both?). If identical -> generic (reduces); if the genuine
divisor propagates differently -> RH-bearing signal.
"""
import mpmath as mp

mp.mp.dps = 60
NZ = 120          # zeros (T_k dominated by low gamma, so this is plenty for small k)
KMAX = 22
DMAX = 9

print(f"dps={mp.mp.dps} NZ={NZ} KMAX={KMAX} DMAX={DMAX}")

# --- zeta reciprocal-seam moments ---
print("computing zeros...")
gammas = [mp.im(mp.zetazero(n)) for n in range(1, NZ + 1)]
print(f"gamma_1={gammas[0]}  gamma_{NZ}={gammas[-1]}")

def T_zeta(k):
    return 2 * mp.fsum((g ** (-2 * k) for g in gammas))

def T_fid(k):
    return mp.zeta(2 * k + 1)

Tz = [T_zeta(k) for k in range(1, KMAX + 1)]   # Tz[k-1] = T_k
Tf = [T_fid(k) for k in range(1, KMAX + 1)]

def hankel(T, d):
    # shifted: H[i,j] = T_{i+j+1} -> T index (i+j+1), stored at T[(i+j+1)-1]=T[i+j]
    return mp.matrix([[T[i + j] for j in range(d)] for i in range(d)])

def eig_sorted(H):
    E = mp.eigsy(H, eigvals_only=False)
    vals, vecs = E
    pairs = sorted(range(len(vals)), key=lambda i: vals[i])
    sv = [vals[p] for p in pairs]
    SV = mp.matrix(H.rows, H.cols)
    for col, p in enumerate(pairs):
        for r in range(H.rows):
            SV[r, col] = vecs[r, p]
    return sv, SV  # ascending eigenvalues, matching eigenvectors as columns

def jacobi_betas(T, nmax):
    # Chebyshev (Stieltjes) algorithm from shifted moments mu_k = T_{k+1} = T[k]
    # Build orthogonal poly recurrence; returns beta_n (squared off-diagonal).
    mu = T[:]  # mu_0 = T_1, mu_1 = T_2, ...
    betas = []
    alphas = []
    try:
        # modified Chebyshev via Hankel determinant ratios (stable enough for small n)
        def hdet(n, shift):
            return mp.det(mp.matrix([[mu[i + j + shift] for j in range(n)] for i in range(n)]))
        prev = mp.mpf(1)
        for n in range(1, nmax + 1):
            d0 = hdet(n, 0)
            d0m = hdet(n - 1, 0) if n >= 1 else mp.mpf(1)
            d0p = hdet(n + 1, 0)
            # beta_n = (D_{n-1} D_{n+1}) / D_n^2  (classical Hankel ratio)
            b = (d0m * d0p) / (d0 * d0)
            betas.append(b)
    except Exception as e:
        betas.append(('err', str(e)))
    return betas

print("\n=== softest-mode / propagation: zeta vs FID ===")
print(f"{'d':>2} | {'lmin_zeta':>14} {'cond_zeta':>12} | {'lmin_fid':>14} {'cond_fid':>12} | {'flexovlp_z':>10} {'flexovlp_f':>10}")
prev_vz = prev_vf = None
for d in range(2, DMAX + 1):
    Hz = hankel(Tz, d); Hf = hankel(Tf, d)
    svz, SVz = eig_sorted(Hz); svf, SVf = eig_sorted(Hf)
    lminz, lmaxz = svz[0], svz[-1]
    lminf, lmaxf = svf[0], svf[-1]
    condz = lmaxz / lminz if lminz != 0 else mp.inf
    condf = lmaxf / lminf if lminf != 0 else mp.inf
    # softest eigenvector (column 0) overlap with previous d (padded)
    vz = [SVz[r, 0] for r in range(d)]
    vf = [SVf[r, 0] for r in range(d)]
    def ovlp(prev, cur):
        if prev is None:
            return mp.mpf('nan')
        n = min(len(prev), len(cur))
        a = [cur[i] for i in range(n)]; b = [prev[i] for i in range(n)]
        na = mp.sqrt(mp.fsum(x * x for x in a)); nb = mp.sqrt(mp.fsum(x * x for x in b))
        if na == 0 or nb == 0:
            return mp.mpf('nan')
        return abs(mp.fsum(a[i] * b[i] for i in range(n)) / (na * nb))
    oz = ovlp(prev_vz, vz); of = ovlp(prev_vf, vf)
    prev_vz, prev_vf = vz, vf
    print(f"{d:>2} | {mp.nstr(lminz,6):>14} {mp.nstr(condz,4):>12} | {mp.nstr(lminf,6):>14} {mp.nstr(condf,4):>12} | {mp.nstr(oz,5):>10} {mp.nstr(of,5):>10}")

print("\n=== Jacobi beta_n (Hankel-ratio), zeta vs FID ===")
bz = jacobi_betas(Tz, min(DMAX, 7))
bf = jacobi_betas(Tf, min(DMAX, 7))
for n in range(len(bz)):
    print(f"beta_{n+1}: zeta={mp.nstr(bz[n],6):>14}   fid={mp.nstr(bf[n],6):>14}")

print("\nDONE. Interpretation key:")
print(" - if flexovlp_z ~ flexovlp_f and beta ratios track -> propagation is GENERIC (reduces to known)")
print(" - if the zeta softest-mode propagates with a DIFFERENT overlap signature than FID -> candidate signal")

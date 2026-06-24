"""
comp88: Verify A_j(k) != 0 for explicit k values.

A_j(k) = j-th Taylor coefficient of g_k(t) = psi(Gamma(-k+t)) + log(t) at t=0.
The multi-k closure argument for psi(Gamma) HT requires A_j(k) != 0 for some k.
Stirling theory predicts: dominant term is (k!)^2 * (H_k - gamma)^{j-2} / (6*(j-2)!) -> +inf.

Method: real-axis polynomial fitting at small positive t (avoids contour pole issues).
At 50-dps precision, polynomial fit at t=0.01..0.10 is stable for j <= 7.

SECRET EXTRA: ratio A_j(k) / [Stirling dominant term] — measuring how fast the
dominant term takes over (should -> 1 as k -> infinity).
"""
import mpmath
import numpy as np

mpmath.mp.dps = 50

def harmonic(k):
    return sum(mpmath.mpf(1)/i for i in range(1, k+1))

def g_k(t, k):
    """g_k(t) = psi(Gamma(-k+t)) + log(t); analytic at t=0+."""
    z = -k + t
    gam = mpmath.gamma(z)
    psi_gam = mpmath.digamma(gam)
    return psi_gam + mpmath.log(t)

def A_j_polyfit(k, j_max=8, t_min=0.005, t_max=0.08, n_pts=30):
    """
    Compute A_j(k) for j=0,...,j_max by polynomial fitting of g_k(t) on [t_min, t_max].
    g_k(t) = sum_{j=0}^{j_max} A_j(k) * t^j + O(t^{j_max+1})
    where A_0(k) = C_k (regular part of psi(Gamma) at the pole), A_1(k) = D_k, etc.
    Returns a dict j -> A_j.
    """
    # Sample points (real, positive, away from t=0)
    ts = [t_min + (t_max - t_min) * i / (n_pts - 1) for i in range(n_pts)]
    ts_mp = [mpmath.mpf(t) for t in ts]

    # Evaluate g_k
    vals = []
    for t in ts_mp:
        try:
            v = g_k(t, k)
            vals.append((t, mpmath.re(v)))  # should be real on the real axis
        except Exception:
            pass  # skip any point that causes a pole

    if len(vals) < j_max + 2:
        return {}

    # Vandermonde fit (using mpmath for stability)
    ts_fit = [v[0] for v in vals]
    ys_fit = [v[1] for v in vals]

    # Build Vandermonde matrix and solve via least squares
    n_terms = j_max + 1
    A_mat = mpmath.matrix(len(ts_fit), n_terms)
    for i, t in enumerate(ts_fit):
        for j in range(n_terms):
            A_mat[i, j] = t**j

    b_vec = mpmath.matrix(ys_fit)

    # Solve least squares: coeffs[j] = A_j
    try:
        # mpmath least squares
        U, S, VT = mpmath.svd(A_mat)
        # pseudo-inverse
        n_svd = min(A_mat.rows, A_mat.cols)
        S_inv = mpmath.matrix(n_terms, n_terms)
        tol = mpmath.mpf(10)**(-40)
        for i in range(n_svd):
            if S[i] > tol:
                S_inv[i, i] = 1 / S[i]

        # Reconstruct solution: coeffs = VT^T * S_inv * U^T * b
        UTb = U.T * b_vec
        S_inv_UTb = S_inv * UTb
        coeffs = VT.T * S_inv_UTb

        return {j: coeffs[j] for j in range(n_terms)}
    except Exception as e:
        return {}

print("=== comp88: Verify A_j(k) != 0 for multi-k closure argument ===")
print(f"Precision: {mpmath.mp.dps} decimal places")
print()

# Compute A_j(k) for k=1..8, j=3,4,5
print("--- A_j(k) for j=3,4,5 and k=1..8 ---")
print("Stirling dominant term for j>=3: (k!)^2 * (H_k-gamma)^{j-2} / (6*(j-2)!)")
print()

results = {}
for k in range(1, 9):
    try:
        coeffs = A_j_polyfit(k, j_max=6, n_pts=40)
        results[k] = coeffs
    except Exception as e:
        print(f"k={k}: FIT ERROR: {e}")

for j in [3, 4, 5]:
    print(f"j={j}:")
    for k in range(1, 9):
        if k not in results or j not in results[k]:
            print(f"  k={k}: MISSING")
            continue
        val = float(results[k][j])
        delta_k = float(harmonic(k) - mpmath.euler)
        if j >= 3 and delta_k > 0:
            from math import factorial
            stir = factorial(k)**2 * delta_k**(j-2) / (6 * factorial(j-2))
            ratio = val / stir if abs(stir) > 1e-15 else float('nan')
        else:
            stir = float('nan')
            ratio = float('nan')
        nonzero = abs(val) > 1e-8
        print(f"  k={k}: A_{j}(k) = {val:+.6f}  stir={stir:.4f}  ratio={ratio:.4f}  {'NONZERO' if nonzero else '*** SMALL ***'}")
    print()

# Focused A_3 check k=1..10
print("--- A_3(k) nonzero check, k=1..12 ---")
all_ok = True
for k in range(1, 13):
    if k not in results:
        try:
            c = A_j_polyfit(k, j_max=6, n_pts=40)
            results[k] = c
        except Exception:
            pass
    val = float(results.get(k, {}).get(3, float('nan')))
    ok = abs(val) > 1e-8
    print(f"  k={k}: A_3 = {val:+.7f}  {'OK' if ok else 'ZERO?'}")
    if not ok:
        all_ok = False

print()
print(f"Conclusion: {'A_3(k) != 0 for all k tested — multi-k closure VERIFIED numerically' if all_ok else 'CHECK k with small A_3'}")

print()
# SECRET EXTRA: Stirling ratio convergence
print("=== SECRET EXTRA: Stirling ratio A_j(k)/dominant_term for j=3,4 ===")
from math import factorial
for j in [3, 4]:
    print(f"j={j} ratio A_j(k) / [(k!)^2*(H_k-gamma)^{{j-2}}/(6*(j-2)!)]:")
    for k in range(2, 9):  # skip k=1 where H_k-gamma = 1-gamma ~ 0.42 (not large)
        val = float(results.get(k, {}).get(j, float('nan')))
        delta_k = float(harmonic(k) - mpmath.euler)
        stir = factorial(k)**2 * delta_k**(j-2) / (6 * factorial(j-2))
        ratio = val / stir if abs(stir) > 1e-12 else float('nan')
        print(f"  k={k}: ratio = {ratio:.5f}  [A_{j}={val:.4g}, stir={stir:.4g}]")
    print()

print("=== Summary ===")
print("If A_j(k) != 0 for some k for each j: multi-k closure argument holds.")
print("Expected: YES, with dominant Stirling term (k!)^2*(H_k-gamma)^{j-2} nonzero for k>=2.")

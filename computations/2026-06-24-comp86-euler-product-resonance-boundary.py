"""
comp86: Verify the resonance theorem boundary.
Resonance theorem predicts: Dirichlet series with k prime terms satisfies no order-n ODE for n < k.
MAIN: check that ζ_{2}(s) = (1-2^{-s})^{-1}(1-3^{-s})^{-1} shows a near-null vector (is DA).
SECRET EXTRA: measure the null-space gap for ζ_{5}(s) = Π_{p≤5}(1-p^{-s})^{-1} (3 primes).
"""
import mpmath
from itertools import combinations_with_replacement
mpmath.mp.dps = 80

def euler_product_jet(s, primes, terms=30):
    """Compute (f, f', f'') for f = Π_p (1-p^{-s})^{-1} via Dirichlet series truncation."""
    s = mpmath.mpc(s)
    f = mpmath.mpc(0)
    df = mpmath.mpc(0)
    d2f = mpmath.mpc(0)
    # sum over n = p1^a1 * p2^a2 * ... with p in 'primes'
    # Enumerate all smooth numbers up to 'terms' terms
    smooth = set([1])
    for p in primes:
        new_smooth = set()
        for n in smooth:
            m = n
            while m <= 10**8:
                new_smooth.add(m)
                m *= p
        smooth = smooth | new_smooth
    smooth = sorted(smooth)[:terms]
    for n in smooth:
        ns = mpmath.power(n, -s)
        log_n = mpmath.log(n)
        f += ns
        df += (-log_n) * ns
        d2f += (log_n**2) * ns
    return f, df, d2f

def zeta_jet(s, terms=50):
    """Compute (f, f', f'') for f = ζ(s) via exact mpmath."""
    s = mpmath.mpc(s)
    f = mpmath.zeta(s)
    df = mpmath.diff(mpmath.zeta, s)
    d2f = mpmath.diff(mpmath.zeta, s, 2)
    return f, df, d2f

def build_monomials(z, f, df, d2f, max_deg):
    variables = [z, f, df, d2f]
    mons = [mpmath.mpc(1)]
    for deg in range(1, max_deg + 1):
        for indices in combinations_with_replacement(range(4), deg):
            m = mpmath.mpc(1)
            for i in indices:
                m *= variables[i]
            mons.append(m)
    return mons

def ode_search(sample_z, jet_fn, max_deg, label):
    from math import comb
    expected_cols = comb(4 + max_deg, max_deg)
    rows_re, rows_im = [], []
    for z in sample_z:
        f, df, d2f = jet_fn(z)
        row = build_monomials(mpmath.mpc(z), f, df, d2f, max_deg)
        assert len(row) == expected_cols
        rows_re.append([mpmath.re(v) for v in row])
        rows_im.append([mpmath.im(v) for v in row])
    M = mpmath.matrix(rows_re + rows_im)
    U, S, VT = mpmath.svd(M)
    S_list = sorted([abs(complex(S[i])) for i in range(min(M.rows, M.cols))])
    ratio = S_list[0] / S_list[-1] if S_list[-1] > 0 else 0
    da_signal = ratio < mpmath.mpf(10)**(-70)
    print(f"  {label}: matrix {M.rows}×{M.cols}, min/max ratio = {ratio:.3e}  {'*** NEAR-NULL (potential ODE)' if da_signal else 'no ODE signal'}")
    return ratio

sample_z = [1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 1.5+0.3j, 2.0+0.5j, 3.0+0.4j, 1.8-0.2j]

print("=== comp86: Resonance boundary — finite vs infinite Euler products ===")
print()

# 2-prime Euler product: ζ_{2}(s) = (1-2^{-s})^{-1}(1-3^{-s})^{-1}
# Resonance theorem says: satisfies no order-1 ODE (1 prime needed); might satisfy order-2 ODE (or might not)
print("MAIN: 2-prime Euler product ζ_{2,3}(s) = (1-2^{-s})^{-1}(1-3^{-s})^{-1}")
jet_23 = lambda s: euler_product_jet(s, [2, 3], terms=20)
for deg in [1, 2, 3]:
    ode_search(sample_z, jet_23, deg, f"ζ_{{2,3}}, degree ≤ {deg}")

print()
print("SECRET EXTRA: ζ(s) (full Riemann zeta, infinitely many primes — resonance theorem predicts HT)")
for deg in [1, 2, 3]:
    ode_search(sample_z, zeta_jet, deg, f"ζ(s), degree ≤ {deg}")

print()
# Also sanity check: f = e^(-s log 2) = 2^{-s} is trivially DA (satisfies f' + (log 2)f = 0)
print("SANITY: f(s) = 2^{-s} (1-prime, trivially DA: f' + (log 2)f = 0)")
jet_2 = lambda s: euler_product_jet(s, [2], terms=10)
ode_search(sample_z, jet_2, 1, "2^{-s}, degree ≤ 1")

print()
print("=== Summary ===")
print("Resonance theorem prediction:")
print("  2^{-s}: DA (1 prime) — should show near-null at order 1 [ABOVE]")
print("  ζ_{2,3}(s): might be DA (2 primes, order could be low)")
print("  ζ(s): HT (infinitely many primes) — should show NO near-null at any order [ABOVE]")

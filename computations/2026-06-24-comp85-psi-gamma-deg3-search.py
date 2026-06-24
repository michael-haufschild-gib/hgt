"""
comp85: Search for polynomial ODE of degree ≤ 3 for f = ψ(Γ(z)).
Extended from comp84 (degree ≤ 2). Same exact chain-rule derivatives.
Secret extra: also measure distance of Taylor coefficients of ψ(Γ) from the
algebraic closure of ℂ(z, ψ(z)) — checks Theorem B2 numerically.
"""
import mpmath
mpmath.mp.dps = 100

def psi_gamma_jet(z):
    """Return (f, f', f'') for f = ψ(Γ(z)) using exact chain rule."""
    z = mpmath.mpc(z)
    G  = mpmath.gamma(z)
    pz = mpmath.digamma(z)
    p1z = mpmath.polygamma(1, z)
    pG  = mpmath.digamma(G)
    p1G = mpmath.polygamma(1, G)
    p2G = mpmath.polygamma(2, G)
    Gp  = pz * G
    Gpp = (p1z + pz**2) * G
    f   = pG
    df  = p1G * Gp
    d2f = p2G * Gp**2 + p1G * Gpp
    return f, df, d2f

# Sample points avoiding poles of Γ
sample_z = [
    0.5, 0.7, 1.3, 1.8, 2.1, 2.5, 3.0, 3.3, 3.7, 4.1, 4.5, 5.0, 5.5, 6.0,
    0.5+0.3j, 0.8+0.5j, 1.2+0.4j, 1.5+0.7j, 2.0+0.2j, 2.5+0.5j, 3.0+0.8j,
    0.5-0.3j, 0.8-0.5j, 1.2-0.4j, 1.5-0.7j, 2.0-0.3j,
    0.3+0.1j, 0.6+0.8j, 1.1-0.6j, 1.8+1.0j, 3.0+0.3j, 4.0+0.6j,
    0.4+1.2j, 0.9+0.9j, 2.2+1.5j, 1.7-1.1j,
]

print("=== comp85: degree ≤ 3 ODE search for f = ψ(Γ(z)) [100 dps, exact chain rule] ===")
data = []
for z in sample_z:
    f, df, d2f = psi_gamma_jet(z)
    data.append((mpmath.mpc(z), f, df, d2f))

from mpmath import matrix

def build_monomials(z, f, df, d2f, max_deg):
    """All monomials z^a * f^b * (f')^c * (f'')^d with a+b+c+d <= max_deg."""
    v = [1, z, f, df, d2f]
    # degree 0: {1}
    mons = [mpmath.mpc(1)]
    # degree 1
    for x in [z, f, df, d2f]:
        mons.append(x)
    if max_deg >= 2:
        for i in range(5):
            for j in range(i, 5):
                mons.append(v[i]*v[j])
    if max_deg >= 3:
        for i in range(5):
            for j in range(i, 5):
                for k in range(j, 5):
                    mons.append(v[i]*v[j]*v[k])
    return mons

def null_space_search(data, max_deg, label):
    print(f"\n=== Null-space search: {label} ===")
    rows_re, rows_im = [], []
    for (z, f, df, d2f) in data:
        row = build_monomials(z, f, df, d2f, max_deg)
        rows_re.append([mpmath.re(v) for v in row])
        rows_im.append([mpmath.im(v) for v in row])
    M = matrix(rows_re + rows_im)
    m, n = M.rows, M.cols
    print(f"  Matrix size: {m}×{n} (columns = # monomials)")
    print(f"  Need m >= n = {n} for full rank; have m = {m}")
    U, S, VT = mpmath.svd(M)
    S_list = sorted([abs(complex(S[i])) for i in range(min(m, n))])
    ratio = S_list[0] / S_list[-1] if S_list[-1] > 0 else 0
    print(f"  Singular values (10 smallest): {[f'{s:.3e}' for s in S_list[:10]]}")
    print(f"  Min/Max ratio: {ratio:.3e}  (< 1e-40 => genuine near-null at 100 dps)")
    if ratio < 1e-40:
        print(f"  *** POTENTIAL ODE RELATION FOUND — check null vector ***")
    else:
        print(f"  No ODE relation at degree <= {max_deg}")
    return ratio

null_space_search(data, 2, "degree <= 2 [100 dps cross-check]")
null_space_search(data, 3, "degree <= 3 [main result]")

# Secret extra measurement: Taylor coefficient distance from alg.closure of C(z, psi(z))
# Theory B2 says psi(Gamma(z)) should NOT be algebraically dependent on psi(z).
# Measure: build monomial matrix for (z, psi(z), psi(Gamma(z))) — algebraic independence test.
print("\n=== EXTRA: algebraic independence of psi(Gamma(z)) from psi(z) over C(z) ===")
print("(Tests Theorem B2: no polynomial P(z, u, v) with P(z, psi(z), psi(Gamma(z))) = 0)")
sample_z2 = [0.5, 0.7, 1.1, 1.5, 2.0, 2.7, 3.2, 0.5+0.3j, 1.0+0.5j, 1.5-0.4j,
             0.8+0.8j, 2.0+0.3j, 3.0-0.2j, 1.2+1.0j, 0.4+0.6j, 2.5+0.7j]
data2 = []
for z in sample_z2:
    z = mpmath.mpc(z)
    u = mpmath.digamma(z)         # psi(z)
    v = mpmath.digamma(mpmath.gamma(z))  # psi(Gamma(z))
    data2.append((z, u, v))

def build_poly_zuu(z, u, v, max_deg):
    vs = [mpmath.mpc(1), z, u, v]
    mons = [mpmath.mpc(1)]
    for x in [z, u, v]:
        mons.append(x)
    if max_deg >= 2:
        for i in range(4):
            for j in range(i, 4):
                mons.append(vs[i]*vs[j])
    if max_deg >= 3:
        for i in range(4):
            for j in range(i, 4):
                for k in range(j, 4):
                    mons.append(vs[i]*vs[j]*vs[k])
    return mons

def alg_indep_test(data2, max_deg, label):
    print(f"\n  Algebraic independence test (degree <= {max_deg}): {label}")
    rows_re, rows_im = [], []
    for (z, u, v) in data2:
        row = build_poly_zuu(z, u, v, max_deg)
        rows_re.append([mpmath.re(x) for x in row])
        rows_im.append([mpmath.im(x) for x in row])
    M = matrix(rows_re + rows_im)
    m, n = M.rows, M.cols
    U, S, VT = mpmath.svd(M)
    S_list = sorted([abs(complex(S[i])) for i in range(min(m, n))])
    ratio = S_list[0] / S_list[-1] if S_list[-1] > 0 else 0
    print(f"    Matrix {m}x{n}, min/max ratio: {ratio:.3e}")
    print(f"    (< 1e-40 => algebraic relation exists; > 1e-5 => algebraically independent)")
    return ratio

alg_indep_test(data2, 2, "z, psi(z), psi(Gamma(z)) — degree 2")
alg_indep_test(data2, 3, "z, psi(z), psi(Gamma(z)) — degree 3")
print("  Expected: no null vector (algebraically independent) — confirming Theorem B2")

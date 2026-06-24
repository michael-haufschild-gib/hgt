"""
comp84: Search for polynomial ODE P(z, f, f', f'') = 0 satisfied by f = ψ(Γ(z)).
Uses EXACT analytic derivatives (chain rule, not finite differences).
Chain rule:
  f  = ψ(Γ(z))
  f' = ψ₁(Γ(z)) · Γ'(z) = ψ₁(Γ(z)) · ψ(z) · Γ(z)
  f''= ψ₂(Γ(z)) · Γ'(z)² + ψ₁(Γ(z)) · Γ''(z)
  Γ'(z) = ψ(z) · Γ(z)
  Γ''(z) = (ψ'(z) + ψ(z)²) · Γ(z) = (ψ₁(z) + ψ(z)²) · Γ(z)
"""
import mpmath
mpmath.mp.dps = 80

def psi_gamma_jet(z):
    """Return (f, f', f'') for f = ψ(Γ(z)) using exact chain rule."""
    z = mpmath.mpc(z)
    G = mpmath.gamma(z)        # Γ(z)
    pz = mpmath.digamma(z)     # ψ(z)
    p1z = mpmath.polygamma(1, z)   # ψ₁(z) = ψ'(z)
    pG = mpmath.digamma(G)     # ψ(Γ(z))
    p1G = mpmath.polygamma(1, G)   # ψ₁(Γ(z))
    p2G = mpmath.polygamma(2, G)   # ψ₂(Γ(z))
    Gp = pz * G                # Γ'(z)
    Gpp = (p1z + pz**2) * G   # Γ''(z)
    f   = pG
    df  = p1G * Gp
    d2f = p2G * Gp**2 + p1G * Gpp
    return f, df, d2f

# Sample points (avoid poles of Gamma at z=0,-1,-2,...)
sample_z = [
    0.5, 0.7, 1.3, 1.8, 2.1, 2.5, 3.0, 3.3, 3.7, 4.1, 4.5, 5.0,
    0.5+0.3j, 0.8+0.5j, 1.2+0.4j, 1.5+0.7j, 2.0+0.2j, 2.5+0.5j,
    0.5-0.3j, 0.8-0.5j, 1.2-0.4j, 1.5-0.7j,
    0.3+0.1j, 0.6+0.8j, 1.1-0.6j, 1.8+1.0j, 3.0+0.3j,
]

print("=== Sampling (z, f, f', f'') for f = ψ(Γ(z)) [exact chain rule] ===")
data = []
for z in sample_z:
    f, df, d2f = psi_gamma_jet(z)
    data.append((mpmath.mpc(z), f, df, d2f))
    print(f"  z={complex(z):.3f}  |f|={abs(complex(f)):.5f}  |f'|={abs(complex(df)):.5f}  |f''|={abs(complex(d2f)):.5f}")

from mpmath import matrix

def build_monomials_deg1(z, f, df, d2f):
    return [1, z, f, df, d2f]

def build_monomials_deg2(z, f, df, d2f):
    v = [1, z, f, df, d2f]
    monomials = list(v)
    for i in range(len(v)):
        for j in range(i, len(v)):
            monomials.append(v[i]*v[j])
    return monomials

def null_space_search(data, builder, label):
    print(f"\n=== Null-space search: {label} polynomial ODE in (z, f, f', f'') ===")
    rows_re, rows_im = [], []
    for (z, f, df, d2f) in data:
        row = builder(z, f, df, d2f)
        rows_re.append([mpmath.re(v) for v in row])
        rows_im.append([mpmath.im(v) for v in row])
    M = matrix(rows_re + rows_im)
    m, n = M.rows, M.cols
    print(f"  Matrix size: {m}×{n}  (should be full rank {n} if no ODE exists)")
    U, S, VT = mpmath.svd(M)
    S_list = [abs(complex(S[i])) for i in range(min(m, n))]
    S_sorted = sorted(S_list)
    ratio = S_sorted[0] / S_sorted[-1] if S_sorted[-1] > 0 else 0
    print(f"  Singular values (sorted): {[f'{s:.3e}' for s in S_sorted[:8]]}")
    print(f"  Min/Max ratio: {ratio:.3e}  (< 1e-30 ⟹ genuine near-null vector)")
    if ratio < 1e-30:
        print(f"  *** POTENTIAL ODE RELATION FOUND ***")
    else:
        print(f"  No low-degree ODE found at this degree")
    return ratio

null_space_search(data, build_monomials_deg1, "degree ≤ 1")
null_space_search(data, build_monomials_deg2, "degree ≤ 2")

# Secret: also check degree ≤ 1 for ψ(Γ(z)) vs f=e^z (sanity checks)
print("\n=== SANITY: f=e^z satisfies f'-f=0, should show null at degree 1 ===")
data_exp = [(mpmath.mpc(z), mpmath.exp(mpmath.mpc(z)), mpmath.exp(mpmath.mpc(z)), mpmath.exp(mpmath.mpc(z)))
            for z in [0.5, 1.0, 1.5, 2.0, 0.5+0.3j, 1.0+0.5j, 1.5-0.3j, 2.0+0.1j]]
null_space_search(data_exp, build_monomials_deg1, "e^z degree ≤ 1 (sanity)")

print("\n=== SANITY: f=ψ(z) is HT (order 0: algebraic?): no degree ≤ 2 in (z,f) alone ===")
data_psi = []
for z in [0.5, 1.0, 1.5, 2.0, 2.5, 0.5+0.3j, 1.0+0.5j, 1.5-0.3j]:
    z = mpmath.mpc(z)
    f = mpmath.digamma(z)
    df = mpmath.polygamma(1, z)
    d2f = mpmath.polygamma(2, z)
    data_psi.append((z, f, df, d2f))
null_space_search(data_psi, build_monomials_deg1, "ψ(z) degree ≤ 1 (HT, no null expected)")

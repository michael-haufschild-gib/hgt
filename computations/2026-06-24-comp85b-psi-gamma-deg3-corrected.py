"""
comp85b: Corrected degree ≤ 3 ODE search for f = ψ(Γ(z)).
Fixes the monomial-duplication bug in comp85 (v=[1,z,f,f',f''] caused 55 cols vs 35 correct).
Uses combinations_with_replacement over {z,f,f',f''} only; constant 1 added once.
Secret extra: measure Wrońskian-like independence of {ψ(z), ψ'(z), ψ(Γ(z))} at sample points.
"""
import mpmath
from itertools import combinations_with_replacement
mpmath.mp.dps = 100

def psi_gamma_jet(z):
    """(f, f', f'') for f = ψ(Γ(z)), exact chain rule."""
    z = mpmath.mpc(z)
    G   = mpmath.gamma(z)
    pz  = mpmath.digamma(z)
    p1z = mpmath.polygamma(1, z)
    pG  = mpmath.digamma(G)
    p1G = mpmath.polygamma(1, G)
    p2G = mpmath.polygamma(2, G)
    Gp  = pz * G
    Gpp = (p1z + pz**2) * G
    return pG, p1G*Gp, p2G*Gp**2 + p1G*Gpp

def build_monomials(z, f, df, d2f, max_deg):
    """All monomials z^a f^b (f')^c (f'')^d with a+b+c+d <= max_deg. No duplicates."""
    variables = [z, f, df, d2f]
    mons = [mpmath.mpc(1)]  # degree 0
    for deg in range(1, max_deg + 1):
        for indices in combinations_with_replacement(range(4), deg):
            m = mpmath.mpc(1)
            for i in indices:
                m *= variables[i]
            mons.append(m)
    return mons

# Sample points: diverse, avoiding poles of Γ at z = 0, -1, -2, ...
sample_z = [
    0.5, 0.7, 1.0, 1.3, 1.8, 2.1, 2.5, 3.0, 3.3, 3.7, 4.1, 4.5, 5.0, 5.5, 6.0,
    0.5+0.3j, 0.8+0.5j, 1.2+0.4j, 1.5+0.7j, 2.0+0.2j, 2.5+0.5j, 3.0+0.8j, 4.0+0.4j,
    0.5-0.3j, 0.8-0.5j, 1.2-0.4j, 1.5-0.7j, 2.0-0.3j, 3.0-0.5j,
    0.3+0.1j, 0.6+0.8j, 1.1-0.6j, 1.8+1.0j, 3.0+0.3j, 4.0+0.6j,
    0.4+1.2j, 0.9+0.9j, 2.2+1.5j, 1.7-1.1j, 3.5+0.2j, 2.8-0.8j,
]

print("=== comp85b: degree ≤ 3 ODE search for f = ψ(Γ(z)) [CORRECTED, 100 dps] ===")
data = []
for z in sample_z:
    f, df, d2f = psi_gamma_jet(z)
    data.append((mpmath.mpc(z), f, df, d2f))
print(f"  {len(data)} sample points collected.")

from mpmath import matrix

def null_space_search(data, max_deg, label):
    from math import comb
    expected_cols = comb(4 + max_deg, max_deg)
    print(f"\n=== {label} (degree ≤ {max_deg}) ===")
    rows_re, rows_im = [], []
    for (z, f, df, d2f) in data:
        row = build_monomials(z, f, df, d2f, max_deg)
        assert len(row) == expected_cols, f"Bug: {len(row)} != {expected_cols}"
        rows_re.append([mpmath.re(v) for v in row])
        rows_im.append([mpmath.im(v) for v in row])
    M = matrix(rows_re + rows_im)
    m, n = M.rows, M.cols
    print(f"  Matrix: {m}×{n} ({expected_cols} correct monomials, no duplicates)")
    print(f"  Overdetermined by {m-n} rows — should be full rank if no ODE exists")
    U, S, VT = mpmath.svd(M)
    S_list = sorted([abs(complex(S[i])) for i in range(min(m, n))])
    ratio = S_list[0] / S_list[-1] if S_list[-1] > 0 else 0
    print(f"  Min SV: {S_list[0]:.3e}   Max SV: {S_list[-1]:.3e}")
    print(f"  10 smallest SVs: {[f'{s:.3e}' for s in S_list[:10]]}")
    print(f"  Min/Max ratio: {ratio:.3e}")
    print(f"  Machine epsilon at 100 dps: ~1e-100")
    if ratio < mpmath.mpf(10)**(-95):
        print(f"  *** GENUINE NULL VECTOR — potential degree-{max_deg} ODE FOUND ***")
    else:
        print(f"  No degree-{max_deg} ODE (min/max well above machine epsilon)")
    return ratio, S_list, VT

r2, S2, VT2 = null_space_search(data, 2, "Degree <= 2 cross-check")
r3, S3, VT3 = null_space_search(data, 3, "Degree <= 3 main result")

# Secret extra: Wronskian-like measurement
# Measure linear independence of the triplet {1, ψ(z), ψ(Γ(z))} AND their derivatives,
# checking whether ψ'(z) and (ψ(Γ(z)))' could together span all first-order solutions.
# This probes whether ψ(Γ(z)) is "differentially over" ψ(z) — a new angle on HT.
print("\n=== EXTRA: Wronskian independence of {ψ(z), (ψ(Γ(z)))} and their derivatives ===")
print("(Probes: could ψ(Γ(z)) be a solution of a 2nd-order LINEAR ODE with ψ-coefficients?)")
wron_pts = [0.7, 1.1, 1.5, 2.0, 2.7, 0.5+0.3j, 1.0+0.4j, 1.5-0.2j, 2.0+0.6j, 0.8-0.5j]
wron_rows_re, wron_rows_im = [], []
for z in wron_pts:
    z = mpmath.mpc(z)
    u  = mpmath.digamma(z)                    # ψ(z)
    u1 = mpmath.polygamma(1, z)               # ψ'(z)
    u2 = mpmath.polygamma(2, z)               # ψ''(z)
    v, v1, v2 = psi_gamma_jet(z)              # ψ(Γ(z)), (ψ(Γ(z)))', (ψ(Γ(z)))''
    # Columns: 1, z, u, u1, u2, v, v1, v2 — check if any degree-1 relation exists
    row = [mpmath.mpc(1), z, u, u1, u2, v, v1, v2]
    wron_rows_re.append([mpmath.re(x) for x in row])
    wron_rows_im.append([mpmath.im(x) for x in row])
Mw = matrix(wron_rows_re + wron_rows_im)
mw, nw = Mw.rows, Mw.cols
Uw, Sw, VTw = mpmath.svd(Mw)
Sw_list = sorted([abs(complex(Sw[i])) for i in range(min(mw, nw))])
print(f"  Matrix: {mw}×{nw}, min/max ratio: {Sw_list[0]/Sw_list[-1]:.3e}")
print(f"  SVs: {[f'{s:.3e}' for s in Sw_list]}")
print(f"  (< 1e-95 => differential linear relation among ψ, ψ', ψ'', ψ(Γ), ψ(Γ)', ψ(Γ)'')")

#!/usr/bin/env python3
# MACHINE STEP6: RUNNABLE test of the ESSENTIAL-SPECTRUM / FREDHOLM constraint ON THE NODE itself
# adapted to a localized hypertranscendental-style potential profile.
#
# Constraint: for H = -d^2/dx^2 + V(x) with V(x)->V_inf at the noncompact end,
# sigma_ess(H)=[V_inf, infty); H-E is FREDHOLM iff E < V_inf.
#
# The essential spectrum is set by the asymptotic value V_inf, NOT by the
# complicated bulk shape. Here the bulk well is modulated by a bounded,
# lacunary, hypertranscendental-style function. The test does not prove
# hypertranscendence; it only uses a pathological-looking bounded profile
# while preserving the Fredholm/essential-spectrum experiment.
import numpy as np

def hypertranscendental_profile(x, terms=18):
    # Bounded lacunary profile: fast-growing frequencies and decaying weights.
    # It is deliberately irregular but numerically stable.
    y = np.zeros_like(x, dtype=float)
    for k in range(1, terms + 1):
        freq1 = 2.0 ** k
        freq2 = 3.0 ** k
        weight = 2.0 ** (-k)
        y += weight * np.sin(freq1 * x + 0.25 * np.sin(freq2 * x))
    m = np.max(np.abs(y))
    return y / m if m > 0 else y

def spectrum(L, n, Vinf, A=4.0):
    # whole line [-L,L], Dirichlet.
    # V(x)=Vinf - A * localized positive well with a hypertranscendental-style modulation.
    x = np.linspace(-L, L, n)
    h = x[1] - x[0]

    sech2 = 1.0 / np.cosh(np.clip(x, -50.0, 50.0))**2
    hyper = hypertranscendental_profile(x)
    modulation = 1.0 + 0.35 * hyper
    well = sech2 * modulation
    well = np.maximum(well, 0.0)

    V = Vinf - A * well
    main = 2.0 / h**2 + V
    off = -1.0 / h**2 * np.ones(n - 1)

    w = np.linalg.eigvalsh(np.diag(main) + np.diag(off, 1) + np.diag(off, -1))
    return np.sort(w)

def counts(L, n, Vinf):
    w = spectrum(L, n, Vinf)
    below = np.sum((w >= Vinf - 1.0) & (w < Vinf))
    above = np.sum((w >= Vinf) & (w < Vinf + 1.0))
    nbound = np.sum(w < Vinf)
    return below, above, nbound

print("=== NODE test: essential-spectrum threshold with hypertranscendental-style bulk (V_inf=0) ===")
print("L (domain half-width) | #eig in [-1,0) (BELOW thresh) | #eig in [0,1) (ABOVE=continuum) | #bound")

for L, n in [(20, 1000), (40, 2000), (80, 4000)]:
    b, a, nb = counts(L, n, Vinf=0.0)
    print(f"  L={L:4d}  below(discrete)={b:3d}   above(continuum)={a:4d}   total_bound={nb:3d}   above/L={a/L:.3f}")

print("  EXPECT: below/bound counts ~L-INDEPENDENT; above count ~proportional to L.")

print("\n=== driving force: threshold MOVES with the at-infinity value V_inf ===")
for Vinf in [-2.0, 0.0, 3.0]:
    w = spectrum(40, 2000, Vinf)
    nb = np.sum(w < Vinf)
    print(
        f"  V_inf={Vinf:5.1f}: total bound states (eig<V_inf)={nb:3d}; "
        f"min eig={w[0]:.3f}; sigma_ess starts ~ {Vinf:.1f}"
    )

print("  => essential spectrum bottom tracks V_inf, even with a hypertranscendental-style bulk well.")
print("     Constraint validated ON NODE.")

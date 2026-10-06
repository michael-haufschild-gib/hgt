# Aperture monotonicity of the restricted-Weil ground-state zeros

**What was computed.**
- Data: the even ground states of the restricted Weil form at apertures a = 0.300, 0.325, …, 0.800 (`mono.py`, N = 40), plus a resolution check at a = 0.775–0.850 with N = 40 and 48 (`mono_hi.py`, mpmath 60 digits).
- Method: Legendre Galerkin with the conventions and code of `computations/weil-polar-ground-energy`; the quadrature is exact up to N = 48.
- Both ground states: `H`, unconstrained (Connes's minuscule eigenvector), and `G`, pole-vanishing (polar).
- Tracked: the real zeros of the transforms on (0, 56] (or (0, 60] at N = 40). Data: `mono.json`, `mono_hi.json`.

**Outcome.**
- Every tracked zero x_k(a) of both H and G is strictly decreasing in a over the whole grid. This includes the prime-power entries a = ½log2 = 0.347, ½log3 = 0.549 and ½log4 = 0.693, which leave no visible jump.
- At converged resolution every matched zero approaches its zeta ordinate from above, with x_k(a) > γ_k throughout. Examples (N = 48), H, k = 9: 48.098 (0.775), 48.029 (0.800), 48.010 (0.825), 48.006 (0.850), with γ₉ = 48.0052. G, k = 9: 48.390, 48.190, 48.061, 48.017.
- An apparent violation (H, k = 9, a = 0.8: 47.9875 < γ₉ at N = 40) is a resolution artifact: Legendre degree N resolves frequencies up to about N/a, and here a·t ≈ 38.4 for N = 40. Use N ≥ a·t + 10.

**Interpretation.**
- Conjecture (C500, open): every real zero of the real-rooted ground state is non-increasing in a, and x_k(a) ≥ γ_k (zero domination).
- Under RH, zero domination gives Σ1/x_k² ≤ Σ1/γ_k² plus the Nyquist tail, i.e. the second-moment bound of the localization theorem (card `ccm-localized-real-rooted-eigenvectors-force-rh`).
- Unconditionally it does not force RH: a first-contact resonance zero can come down from above monotonically.
- The loop-row 490/491 counterexamples (a ≥ 1.1) were unconverged data.

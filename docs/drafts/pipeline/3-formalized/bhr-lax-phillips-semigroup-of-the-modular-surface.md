# BHR — the Lax–Phillips semigroup of the modular surface

- **ID:** bhr-modular-lax-phillips (review-0711 A27, Lax–Phillips item)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `u` range over resonances of `SL₂(ℤ)\ℍ`: `Λ(1+2u) = 0`, `−½ < Re u < 0`, `Im u > 0` (so `u = (ρ−1)/2`), and `t_u = Λ¹E*_u ∈ L²(𝒟)` the resonant state truncated at height `1`. With the outgoing cusp model `F ↦ (Z(t)F)(y) = 1_{(0,1]}(y) e^{−t/2}F(e^{−t}y)` (compressed normalized dilation):
  1. `Z(t) t_u = e^{ut} t_u` in the cusp model;
  2. for every finite combination and `t ≥ 0`, `‖Σ cᵢ e^{uᵢt} t_{uᵢ}‖²_{L²(𝒟)} = ∫₀^{e^{−t}} |Σ cᵢ Λ(2uᵢ) y^{−uᵢ−½}|² dy`;
  3. hence `Z(t)` is a contraction semigroup on the span of the resonant states (well defined), and `‖Z(t)f‖ → 0` as `t → ∞`;
  4. `‖Z(t)t_u‖² = e^{2Re u·t}‖t_u‖²`, `‖t_u‖² > 0`, and RH ⟺ every resonant mode decays at the universal rate `‖Z(t)t_u‖² = e^{−t/2}‖t_u‖²`.

## Proof
1. `cuspCutoff_dilation` with `r = e^{−t}`: `√r·c_u(ry) = r^{−u}c_u^{(1/r)}(y)`, `r^{−u} = e^{ut}`, and the cut at height `1 ≤ 1/r` restores `c_u^{(1)}`.
2. `resonant_finite_combination_isometry` (corpus) moves the left side into the cusp model, (1) and linearity identify it with `Z(t)` of the model vector, and the substitution `x = e^{−t}y` gives `∫|Z(t)F|² = ∫₀^{e^{−t}}|F|²`.
3. Monotonicity of the set integral; dominated convergence on the shrinking sets `(0, e^{−t}]`.
4. Scaling of the norm; `‖t_u‖² = ∫₀¹|Λ(2u)|²y^{−2Re u−1} > 0` since `Λ(2u) = Λ(ρ−1) ≠ 0`. A zero with `Re ρ > ½` (upper half plane by conjugation, none on the real segment) gives a resonance with `2Re u ≠ −½`.

Dictionary: the graph semigroup `lpMatrix` (compression of the wave group, spectrum = modes) and `kreinHerm_nonneg_iff` (Hilbert metric iff universal damping) of `ArithmeticScatteringHolography.TheLaxPhillipsSemigroup`. On the modular surface the metric is always Hilbert (actual `L²` states); the RH content is the decay rate `1/4` of every mode, the same `1/4` as in Zagier's exponent `3/4 = 1/2 + 1/4` (`bhr-zagier-horocycle-rate-is-the-zero-free-region.md`). The Gram matrix of the modes is the Szegő kernel at the zeros of the Blaschke product `ξ(2s−1)/ξ(2s)` (`integral_resonant_gram_eq_szego`), i.e. this is the functional model of `Z(t)`.

## Lean
`formal/GaloisForLFunctions/BlackHoleRingdown/TheLaxPhillipsSemigroupOfTheModularSurface.lean`: `lpCompress`, `lpCompress_cuspCutoff`, `lpCompress_sum`, `integral_norm_sq_lpCompress`, `integral_norm_sq_resonantFlow`, `integral_norm_sq_resonant`, `resonantFlow_contraction`, `resonantFlow_eq_zero`, `tendsto_resonantFlow_zero`, `integral_norm_sq_mode`, `integral_norm_sq_resonantState_pos`, `riemannHypothesis_iff_resonant_decay`. Checked with `lake --old env lean`; axioms `propext, Classical.choice, Quot.sound`.

## Scope
The semigroup is constructed on the span of the resonant states (the Eisenstein part of the interaction space); cusp forms, which are eigenvectors of the full Lax–Phillips generator with purely imaginary exponents, are not included.

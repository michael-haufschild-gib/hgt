# TG — extremal Bessel inequality and the attainment criterion

- **ID:** TG-BOHR-3
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Statement:** g(u) = e^{-(Θ−½)u/2}G(e^{-u}), G the central Gaussian gap, Θ = sup Re ρ.
  (a) Window Bessel: |T⁻¹∫₀^T f e^{-iτu}|² ≤ T⁻¹∫₀^T |f|².
  (b) ∀τ, ε>0: eventually |A(½)[Θ=½∧τ=0] − Σ_{Re ρ=Θ, Im ρ=2τ}½Γ((ρ−½)/2)|² − ε ≤ T⁻¹∫₀^T g².
  (c) Θ > ½ ⇒ (∃ zero on Re ρ = Θ ⟺ T⁻¹∫₀^T g² does not tend to 0).

## Proof
(a) m = T⁻¹∫|f| ≥ |avg|, and ∫(|f|−m)² ≥ 0. (b) TG-BOHR-2 window limit + (a). (c) ⇒ by (b) at τ = Im ρ₀/2
(nonzero coefficient by visibility); ⇐ with no extremal zero the extremal series vanishes and Θ ≠ ½, so
g → 0 and the Cesàro means of g² → 0.

## Lean
`RHTower/GaussianWeightedGapExtremalBessel.lean`, wired after GaussianTopologicalGateEquivalences.
`norm_gaussianWindowAverage_mul_cexp_sq_le`, `eventually_extremalBohr_sq_le_meanSquare`,
`extremal_zero_exists_iff_not_tendsto_meanSquare`. Build exit 0; axioms [propext, Classical.choice, Quot.sound].

## Reading
TG-shaped trace inequality "zero Gram (extremal line) ≤ prime-side mean square", unconditional; and a
prime-side criterion for whether the zero abscissa is attained. If RH fails, either the extremal
off-line zeros are visible in the mean square, or Θ is unattained and the normalized gap is o(1).

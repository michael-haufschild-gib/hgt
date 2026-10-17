# Card: Foundational Blueprint & Initial Formalization of Bi-Scale / Logarithmic-Grid Uncertainty Theory

- **Stage**: `3-formalized`
- **Date**: `2026-10-17`
- **Area**: `GaloisForLFunctions.BiScaleUncertainty`
- **Umbrella**: `formal/GaloisForLFunctions/BiScaleUncertainty.lean`
- **Treatise / Blueprint**: `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`

## Formalized Modules & Key Theorems

1. **Pillar I — `formal/GaloisForLFunctions/BiScaleUncertainty/KreinIncrementAndChordCascade.lean`**
   - `integral_shift_sub_shift_sq`, `integral_add_shift_sq`, `abs_autocorr_le_zero`:
     Exact `L²` sum/difference identities and Cauchy–Schwarz envelope `|h(x)| ≤ h(0)`.
   - `autocorr_chord_peter_paul`, `autocorr_sqrt_sub_add_le`:
     Peter–Paul chord inequality and exact subadditive chord triangle law
     `√(h(0) - h(x + y)) ≤ √(h(0) - h(x)) + √(h(0) - h(y))`.
   - `autocorr_sub_two_mul_le`, `autocorr_sub_nat_mul_le`, `autocorr_sub_pow_two_mul_le`:
     Krein doubling (`h(0) - h(2x) ≤ 4(h(0) - h(x))`), quadratic multiple cascade
     (`h(0) - h(m x) ≤ m^2 (h(0) - h(x))`), and dyadic cascade (`h(0) - h(2^k x) ≤ 4^k (h(0) - h(x))`).
   - `autocorr_harmonic_subgrid_ge_of_nonpos`, `autocorr_dyadic_subgrid_ge_of_zero`:
     Derivative-free harmonic and dyadic sub-grid lower bounds at any zero or nonpositive node.
   - `autocorr_krein_increment_sq_le`, `autocorr_sq_le_two_mul_sub_of_zero`:
     Krein's positive-definite increment inequality `(h(x) - h(y))^2 ≤ 2 h(0) (h(0) - h(x - y))`.

2. **Pillar II — `formal/GaloisForLFunctions/BiScaleUncertainty/MultiplicativeChainBesselAndOriginLeverage.lean`**
   - `autocorr_finset_bessel_sq_le`:
     Multi-node orthogonal-frame Bessel inequality `∑ i ∈ s, h(y - t_i)^2 ≤ h(0)^2` for any
     pairwise difference-orthogonal shift family.
   - `autocorr_origin_chain_sphere_sub_le`, `autocorr_origin_chain_sphere_add_le`,
     `autocorr_reflected_collar_sphere_le`, `autocorr_reflected_collar_sum_sub_ge`:
     Origin-anchored left/right-collar Euclidean Sphere Laws
     `h(y)^2 + ∑ i ∈ s, h(t_i ∓ y)^2 ≤ h(0)^2` and the reflected-collar defect law
     `(2 - √2) h(0) ≤ (h(0) - h(y)) + (h(0) - h(t₁ - y))`.
   - `origin_singularity_leverage_sphere_bound`, `origin_singularity_leverage_rational_bound`,
     `autocorr_origin_singularity_leverage_sub`:
     The Origin-Singularity Leverage Theorem coupling the singular origin weight `W₀ > 0` to
     collar weights `w_i ≥ 0` with only an `O(1 / W₀)` defect `(∑ w_i^2) / (2 W₀)`.
   - `log_sub_log_mem_Icc_of_dvd`, `autocorr_log_divisibility_pair_orth`,
     `autocorr_dyadic_coset_sphere_sub_le`:
     Exact difference-orthogonality of divisibility chains and dyadic-odd cosets
     `𝒞_m = {m · 2^k}` on the logarithmic grid `Λ_N = {log n : 2 ≤ n ≤ N}`.

3. **Pillar III — `formal/GaloisForLFunctions/BiScaleUncertainty/HyperbolicPolarBalanceAndLevySinhFunctional.lean`**
   - `weilArchRe_eq_polar_levy_sinh_form`, `weilArchRe_nonneg_iff_levy_sinh_ge_abs_gammaBracket`:
     Exact pole-eliminated Weil–Lévy identity and equivalence between archimedean positivity on the
     polar hyperplane and `|Ω(0)| h(0) ≤ biScaleLevyEnergy f`.
   - `autocorrPos_sub_autocorrNeg`, `autocorrPos_le_zero`,
     `integral_autocorrPos_cosh_eq_autocorrNeg_cosh`:
     Positive/negative lobe decomposition `h = h⁺ - h⁻` and exact conservation of hyperbolic lobe
     mass `∫_{(0, ∞)} h⁺(x) cosh(x / 2) = ∫_{(0, ∞)} h⁻(x) cosh(x / 2)` on the polar hyperplane.
   - `polar_levy_deformation_identity`, `polar_levy_lobe_split_identity`,
     `polar_levy_deformation_lower_bound`:
     Polar–Lévy kernel deformation identity and crossover floor.

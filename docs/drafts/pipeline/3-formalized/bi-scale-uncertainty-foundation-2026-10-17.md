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

4. **Pillar IV — `formal/GaloisForLFunctions/BiScaleUncertainty/FoldedCollarIntegralAndObstructionResolution.lean`**
   - `autocorr_weighted_reflected_pair_ge_sphere`, `autocorr_weighted_reflected_pair_ge_min`:
     Weighted reflected-collar sphere lower bound
     `w₁(h(0) - h(y)) + w₂(h(0) - h(t₁ - y)) ≥ (w₁ + w₂ - √(w₁² + w₂²)) h(0) ≥ (2 - √2) min(w₁, w₂) h(0)`
     resolving the single-point non-dyadic obstruction at `x = 4 log 2 / 5`.
   - `intervalIntegral_fold_midpoint`, `integral_autocorr_sub_mul_ge_folded_sphere`:
     Midpoint interval-folding identity and folded-collar integral lower bound on `[a, t₁ - a]`.
   - `biScaleLevyEnergy_ge_folded_collar_integral`, `archFoldedCollarConstant_pos`:
     Unconditional strictly positive lower bound `archFoldedCollarConstant a (Real.log 2) * h(0) ≤ biScaleLevyEnergy f`
     from a single zero node `h(log 2) = 0`.
   - `RealSmoothEvenPolarTestFn.weilArchRe_ge_folded_collar_of_log_two_blind`:
     Direct specialization to smooth real EWU tests (`RealSmoothEvenPolarTestFn`).

5. **Pillar V — `formal/GaloisForLFunctions/BiScaleUncertainty/CliqueSphereDualityAndExtremalTheory.lean`**
   - `clique_sphere_quadratic_defect_identity`, `clique_sphere_weighted_sub_ge`:
     Division-free quadratic sphere defect identity and multi-node clique sphere lower bound
     `cliqueSphereDualityFactor s w * R ≤ ∑ i ∈ s, w_i (R - u_i)`.
   - `clique_sphere_extremizer_norm_sq`, `clique_sphere_extremizer_achieves_bound`:
     Exact extremal saturation on the Euclidean sphere along the ray `u_i* = (w_i / W₂) R`.
   - `autocorr_weighted_clique_collar_ge`, `autocorr_clique_uniform_collar_sum_ge`,
     `integral_autocorr_clique_collar_ge`:
     Clique-Rank Amplification Law `((s.card : ℝ) - √(s.card : ℝ)) * h(0) ≤ ∑ i ∈ s, (h(0) - h(y - t_i))`
     and multi-node clique collar integral lower bound.

6. **Pillar VI — `formal/GaloisForLFunctions/BiScaleUncertainty/HyperbolicShiftCommutatorAndParityIntertwining.lean`**
   - `sinhMultiplier_even_of_odd`, `coshMultiplier_odd_of_odd`,
     `cosh_mul_cosh_shift_sub_sinh_mul_sinh_shift`, `sinh_shift_mul_cosh_sub_cosh_shift_mul_sinh`:
     Odd-to-even hyperbolic parity intertwining and exact pointwise shift-addition/commutator laws.
   - `autocorr_coshMultiplier_sub_sinhMultiplier`, `autocorr_coshMultiplier_zero_eq`,
     `autocorr_coshMultiplier_eq_sinhMultiplier_of_zero`:
     The Fundamental Hyperbolic Autocorrelation Intertwining Law
     `autocorr (coshMultiplier α f) x - autocorr (sinhMultiplier α f) x = cosh(α x) * autocorr f x`
     and zero-grid coincidence of `cosh`- and `sinh`-autocorrelations.
   - `autocorr_coshMultiplier_sub_ge_of_zero`,
     `autocorr_coshMultiplier_harmonic_subgrid_ge_of_nonpos`:
     Unconditional `cosh`-increment coercivity `h(0) ≤ h_{C_α f}(0) - h_{C_α f}(x₀)` at zero nodes
     and `h(0) / m^2 ≤ h_{C_α f}(0) - h_{C_α f}(x₀ / m)` on harmonic sub-grids.

7. **Pillar VII — `formal/GaloisForLFunctions/BiScaleUncertainty/CoprimeShearAndMultiplicativeGraphUncertainty.lean`**
   - `addDiff_mulShift_eq_sum_addDiff`, `mulShift_addShift_comm_eq_sum_addDiff`,
     `mulJump_eq_sum_addDiff`:
     Exact non-commutative multiplicative-additive telescoping identities.
   - `lagrange_finset_sum_sq_sub_sq_sum`, `sq_sum_le_card_mul_sum_sq`,
     `sum_addDiff_mulShift_sq_le`:
     Bi-Scale Multiplicative-to-Additive Dirichlet Energy Inequality
     `∑ n ∈ range N, (v(k(n + 1)) - v(kn))^2 ≤ k * ∑ m ∈ range (k * N), (v(m + 1) - v(m))^2`.
   - `not_dvd_succ_of_dvd`, `addDiff_sq_eq_sq_of_dvd_support`,
     `neighbor_addDiff_sq_eq_two_mul_sq_of_dvd_support`:
     Coprime successor orthogonality (`gcd(n, n + 1) = 1`) and full additive neighbor coercivity on
     divisor-supported fibers.
   - `nodal_mulJump_sq_decomp`, `four_mul_nodal_cross_le_mulJump_sq`,
     `four_mul_nodal_cross_le_addDiff_sum_sq`:
     Beurling–Deny nodal decomposition `(v(kn) - v(n))^2 = (|v(kn)| - |v(n)|)^2 + 4(v⁺(kn)v⁻(n) + v⁻(kn)v⁺(n))`
     and additive Dirichlet control of opposite-sign multiplicative cross terms.

8. **Pillar VIII — `formal/GaloisForLFunctions/BiScaleUncertainty/AbstractBiScaleSystemAndSchurKreinCoupling.lean`**
   - `inner_scaledFrameResidual_eq`, `norm_sq_scaledFrameResidual_eq`, `abstract_finset_bessel_sq_le`:
     Division-free orthogonal-frame residual identity and Bessel inequality in any real inner
     product space `E`.
   - `abstract_schur_krein_residual_coupling`, `abstract_orthogonal_target_frame_inner_sq_le`:
     Universal Multi-Node Schur–Krein Residual Coupling Inequality
     `(R ⟪x, y⟫ - ∑ i ∈ s, ⟪e_i, x⟫ ⟪e_i, y⟫)^2 ≤ (R ‖x‖^2 - ∑ i ∈ s, ⟪e_i, x⟫^2) (R ‖y‖^2 - ∑ i ∈ s, ⟪e_i, y⟫^2)`.
   - `autocorr_schur_krein_two_collar_coupling`, `autocorr_collar_inner_sq_le_of_zero_lag`:
     Two-collar autocorrelation coupling across arbitrary lags and across a zero lag `h(z - y) = 0`.

9. **Pillar IX — `formal/GaloisForLFunctions/BiScaleUncertainty/CosecantSecantDualDecomposition.lean`**
   - `archLevySinhWeight_eq_half_csch_add_half_sech`, `archDualLevySinhWeight_eq_half_csch_sub_half_sech`,
     `archLevySinhWeight_eq_sech_add_dual`:
     Exact cosecant–secant and forward–dual decompositions
     `e^{x/2}/sinh x = 1/cosh(x/2) + e^{-x/2}/sinh x`.
   - `biScaleLevyEnergy_eq_secant_add_dual`, `biScaleSecantEnergy_le_biScaleLevyEnergy`,
     `biScaleDualLevyEnergy_le_biScaleLevyEnergy`:
     Exact positive splitting of `biScaleLevyEnergy` into the smooth secant functional and the
     functional-equation dual Lévy–sinh functional.
   - `autocorr_mul_archSechHalfWeight_eq_cosh_sub_sinh`:
     Exact identity between `h_f(x) / cosh(x/2)` and the `α = 1/4` hyperbolic multiplier difference.

10. **Pillar X — `formal/GaloisForLFunctions/BiScaleUncertainty/DisjointCollarCliqueDivergenceAndTuransProblem.lean`**
    - `intervalIntegral_periodic_collar_sum_eq`, `intervalIntegral_periodic_collar_sum_eq_of_continuousOn`:
      Exact periodic-collar tiling identities on `[t₀, t₀ + K δ]`.
    - `integral_periodic_clique_weighted_sub_ge`, `integral_autocorr_sub_ge_of_arithmetic_zeros`:
      Weighted periodic-clique integral bound and the Beurling–Turán Window Divergence Theorem
      `δ ((M + 1) - √(M + 1)) h(0) ≤ ∫ x in 0..((M + 1) * δ), (h(0) - h(x))`.
    - `integral_autocorr_le_sqrt_of_arithmetic_zeros`:
      Universal Square-Root Cancellation Law `∫ x in 0..((M + 1) * δ), h(x) ≤ δ √(M + 1) h(0)` for
      any positive-definite autocorrelation vanishing at `m δ` (`1 ≤ m ≤ M`).
    - `biScaleLevyEnergy_ge_dyadic_clique_integral`:
      Unconditional dyadic-clique lower bound `dyadicCliqueLevyConstant M * h(0) ≤ biScaleLevyEnergy f`
      for `C²_c(ℝ)` functions vanishing at `m log 2` (`1 ≤ m ≤ M`).

## Audit Status
- **Umbrella Verification**: `lake env lean GaloisForLFunctions/BiScaleUncertainty.lean` passes with exit code `0` (all 25 modules wired).
- **Axiom Audit**: `#print axioms` verified on all key theorems across Pillars I–X; every declaration depends only on `[propext, Classical.choice, Quot.sound]`, with zero `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations.


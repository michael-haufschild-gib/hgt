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

11. **Pillar XI — `formal/GaloisForLFunctions/BiScaleUncertainty/MultiCosetGramPackingAndNyquistDensity.lean`**
    - `inner_sum_self_eq_double_sum`, `norm_sq_sub_linearComb_eq`,
      `sum_inner_sq_sq_le_norm_sq_mul_gram_quad`, `gram_quad_le_of_row_sum_bound`,
      `abstract_selberg_bombieri_bessel_le`:
      Selberg–Bombieri almost-orthogonal Gram row-sum Bessel inequality
      `∑_{i ∈ s} ⟪e_i, x⟫² ≤ M_row ‖x‖²` in any real inner product space `E`.
    - `autocorr_almost_orthogonal_bessel_sq_le`, `almost_orthogonal_collar_uniform_sum_ge`:
      Multi-coset Selberg–Bombieri Bessel bound and collar amplification law
      `((s.card : ℝ) - √((s.card : ℝ) * (1 + Δ))) * h_f(0) ≤ ∑_{i ∈ s} (h_f(0) - h_f(y - t_i))`.
    - `log_succ_sub_log_pos`, `log_succ_sub_log_le_inv`, `log_succ_sub_log_antitone`,
      `archLevySinhWeight_ge_nat_on_nyquist_collar`:
      Nyquist step bounds `0 < log(n + 1) - log n ≤ 1 / n` and origin-singularity absorption
      `(n : ℝ) ≤ archLevySinhWeight y` on `(0, log(n + 1) - log n]`.
    - `intervalIntegral_dyadic_log_partition_eq`,
      `integral_autocorr_sq_dyadic_window_le_sum_collar`,
      `integral_autocorr_sq_dyadic_window_le_levy_collar`,
      `integral_autocorr_sq_dyadic_window_le_biScaleLevyEnergy`:
      Derivative-free `L²` Nyquist compression across the `N` cells in `[log N, log(2N)]` absorbed by
      the origin singularity `archLevySinhWeight y ≥ N`.

12. **Pillar XII — `formal/GaloisForLFunctions/BiScaleUncertainty/ProducerConsumerDualityAndNymanBeurlingBridge.lean`**
    - `producer_consumer_defect_eq`, `producer_consumer_inner_eq`,
      `producer_consumer_defect_sq_le`, `consumer_polar_sq_le_producer_error`:
      Abstract Hilbert-space Producer–Consumer Duality coupling grid-blind consumers `⟪f, g_i⟫ = 0`
      to producer `L²` approximation errors `‖p - ∑_{i ∈ s} c_i g_i‖²`.
    - `fzzp_nyman_beurling_orthogonal_duality_identity`:
      Exact FZZ-P / Nyman–Beurling orthogonal duality identity
      `R ‖p - ∑_{i ∈ s} c_i e_i‖² = (R ‖p‖² - ∑_{i ∈ s} ⟪e_i, p⟫²) + ∑_{i ∈ s} (R c_i - ⟪e_i, p⟫)²`.
    - `intervalIntegral_cauchy_schwarz_sq_le`,
      `correlation_polar_producer_decomposition`,
      `correlation_producer_consumer_residual_sq_le`,
      `dyadic_window_producer_consumer_duality_le_levy`:
      Correlation-space polar–producer decomposition and dyadic-window duality bound controlled by
      the origin-collar Lévy integral.

13. **Pillar XIII — `formal/GaloisForLFunctions/BiScaleUncertainty/AsymptoticTailCoercivityAndNyquistTrap5Closure.lean`**
    - `integral_autocorr_sub_le_cube_of_quad_collar`,
      `integral_autocorr_sq_dyadic_window_le_of_quad_collar`:
      `O(N⁻²)` dyadic-window `L²` correlation decay `∫_{log N}^{log(2N)} h_f(x)² dx ≤ (2 K / N²) h_f(0)`
      under quadratic origin-collar regularity `h_f(0) - h_f(y) ≤ K y²` on `[0, 1 / N]`.
    - `cosh_half_sq_le_two_mul_nat_on_dyadic_window`,
      `integral_cosh_half_sq_dyadic_window_le`:
      `O(N)` hyperbolic polar weight energy bound `∫_{log N}^{log(2N)} cosh(x / 2)² dx ≤ 2 N log 2`.
    - `integral_abs_autocorr_mul_cosh_dyadic_window_sq_le`,
      `integral_autocorrNeg_mul_cosh_dyadic_window_sq_le`,
      `infinite_grid_distant_lobe_kinetic_coercivity`,
      `integral_abs_autocorr_mul_cosh_dyadic_window_sq_le_levy`:
      `O(N⁻¹/²)` dyadic-window polar tail decay and the Infinite-Grid Trap-5 Closure / Kinetic
      Coercivity Theorem `N μ² ≤ 4 log 2 K h_f(0)`.

14. **Pillar XIV — `formal/GaloisForLFunctions/BiScaleUncertainty/SignedKreinCollarAndPrimeDeficitTransfer.lean`**
    - `autocorr_signed_collar_add_eq`, `autocorr_signed_collar_sub_eq`,
      `autocorr_signed_collar_add_ge_krein`, `autocorr_signed_collar_sub_ge_krein`,
      `autocorr_signed_collar_origin_leverage_add`, `autocorr_signed_collar_origin_leverage_sub`:
      Exact signed collar-increment decomposition `(h_f(0) - h_f(t ± y)) + h_f(t) = h_f(0) - (h_f(t ± y) - h_f(t))`
      and single-node origin-collar leverage for arbitrary signed `h_f(t) ∈ ℝ` (resolving Trap 9).
    - `abstract_signed_collar_gram_identity`, `abstract_signed_collar_gram_ge`,
      `abstract_signed_clique_origin_leverage_ge`, `abstract_signed_almost_orthogonal_origin_leverage_ge`:
      Abstract Hilbert-space completion-of-squares identity and multi-node signed collar leverage
      for orthogonal cliques and Selberg–Bombieri almost-orthogonal families without blindness
      assumptions.
    - `sum_integral_signed_nyquist_collar_ge`:
      Signed dyadic-window Nyquist sum-to-integral collar bound across `[log N, log(2N)]`.
    - `archLevySinhWeight_log_nat_eq`, `archLevySinhWeight_log_nat_ge_two_div_sqrt`,
      `archLevySinhWeight_log_nat_sub_two_div_sqrt_le`:
      Exact critical-line `2 / √n` node scaling law and `O(n^{-5/2})` remainder bound for
      `archLevySinhWeight (log n)` (`n ≥ 2`).

15. **Pillar XV — `formal/GaloisForLFunctions/BiScaleUncertainty/KreinKantorovichMeasureTransportAndPrimePolarPairing.lean`**
    - `inv_archLevySinhWeight_eq`, `exp_neg_half_mul_sinh_eq`, `exp_neg_half_mul_sinh_le`,
      `archLevySinhWeight_ge_exp_neg_half_div`:
      Linear origin-vanishing bound `(archLevySinhWeight y)⁻¹ = exp(-y / 2) * sinh y ≤ y * exp(y / 2)`
      and singular hyperbolic lower bound `exp(-r₂ / 2) / y ≤ archLevySinhWeight y` on `(0, r₂]`.
    - `krein_kantorovich_pointwise_abs_le`, `krein_kantorovich_pointwise_linear_reg_le`,
      `collar_measure_transport_abs_diff_le_levy`:
      Pointwise and integrated Krein–Kantorovich measure-transport inequalities coupling discrete
      node evaluations `h_f(t)` to continuum collar integrals `∫_a^δ h_f(t + y) ρ(y) dy`.
    - `narrow_support_logarithmic_levy_lower_bound`, `bounded_levy_width_rigidity`:
      Logarithmic archimedean energy cost `exp(-r₂ / 2) log(r₂ / r₁) h_f(0)` of narrow support and
      Bounded-Energy Width Rigidity `log(r₂ / r₁) ≤ exp(r₂ / 2) K` (closing Trap 8 in the
      bounded-energy regime).

16. **Pillar XVI — `formal/GaloisForLFunctions/BiScaleUncertainty/HyperbolicMultiplierIncrementAndOddSignCoercivity.lean`**
    - `coshMultiplier_defect_add_sinh_half_sq_eq`,
      `sinhMultiplier_defect_le_coshMultiplier_defect`,
      `cosh_mul_source_defect_le_coshMultiplier_defect`:
      Exact two-positive-term hyperbolic multiplier defect decomposition and two-way domination
      bounds.
    - `sinhMultiplier_signed_collar_origin_leverage_add`,
      `coshMultiplier_signed_collar_origin_leverage_add`,
      `coshMultiplier_signed_collar_ge_of_source_zero`,
      `joint_base_sinhMultiplier_collar_ge_of_source_zero`:
      Leakage-proof signed collar leverage for `S_α f` and `C_α f`, and zero-grid coincidence lift
      resolving Trap 7 (`OddMultiplierLeakageFamily.lean`).

17. **Pillar XVII — `formal/GaloisForLFunctions/BiScaleUncertainty/EulerMaclaurinLevyQuadratureAndSFreeCellBounds.lean`**
    - `cell_quadrature_diff_eq_shifted_integral`, `pointwise_weighted_krein_cell_bound`,
      `cell_quadrature_abs_diff_le_origin_collar`:
      Everywhere-continuous, $S(f)$-free Euler–Maclaurin cell quadrature bounds eliminating Trap 1.
    - `nyquist_cell_origin_integral_le_levy`, `nyquist_cell_quadrature_abs_diff_le_levy`,
      `dyadic_window_global_quadrature_abs_diff_le_biScaleLevyEnergy`:
      Origin-singularity absorption on Nyquist cells `[log n, log(n+1)]` and global dyadic-window
      quadrature bounds controlled by a single copy of `biScaleLevyEnergy`.
    - `integral_exp_half_log_cell_eq`, `integral_exp_half_sq_log_cell_eq`,
      `nyquist_polar_cell_quadrature_abs_diff_le_levy`,
      `RealEvenPolarTestFn.unconditional_polar_cell_quadrature_bound`:
      Exact polar cell integrals and unconditional polar quadrature bound on `RealEvenPolarTestFn`.

18. **Pillar XVIII — `formal/GaloisForLFunctions/BiScaleUncertainty/MultiShellOriginBudgetAndGlobalPrimeCollarSynthesis.lean`**
    - `archLevySinhWeight_eq_two_div_of_pos`, `archLevySinhWeight_antitoneOn`,
      `two_div_sqrt_succ_le_archLevySinhWeight`, `nyquist_shifted_collar_le_levy_cell`:
      Strict antitonicity of `archLevySinhWeight` on `(0, ∞)` and critical-line collar dominance.
    - `origin_add_tail_levy_eq_biScaleLevyEnergy`, `nyquist_step_le_log_self`,
      `origin_add_dyadic_window_levy_le_biScaleLevyEnergy`:
      Disjoint origin-plus-tail partition of `biScaleLevyEnergy`.
    - `nyquist_cell_adaptive_signed_coercivity`, `global_dyadic_nyquist_signed_coercivity`:
      Unconditional global dyadic Nyquist signed coercivity across `[log N, log(2N)]`.

19. **Pillar XIX — `formal/GaloisForLFunctions/BiScaleUncertainty/SignedWeilFunctionalCoercivityAndRHBridge.lean`**
    - `dyadicNyquistCoerciveConstant`, `two_div_sqrt_sub_two_div_pos`,
      `dyadicNyquistCoerciveConstant_pos`:
      Strict positivity of the concrete dyadic Nyquist coercive constant `dyadicNyquistCoerciveConstant (M + 2)`.
    - `RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy`,
      `RealEvenPolarTestFn.unconditional_dyadic_signed_weil_lower_bound`,
      `RealEvenPolarTestFn.unconditional_single_node_signed_weil_lower_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_dyadic_signed_weil_lower_bound`:
      100% unconditional signed Weil functional lower bounds on `RealEvenPolarTestFn` and
      `RealSmoothEvenPolarTestFn`.
    - `RealEvenPolarTestFn.unconditional_coshMultiplier_dyadic_signed_coercivity`,
      `RealEvenPolarTestFn.unconditional_sinhMultiplier_dyadic_signed_coercivity`:
      Unconditional hyperbolic multiplier dyadic Nyquist signed coercivity.

20. **Pillar XX — `formal/GaloisForLFunctions/BiScaleUncertainty/AllScaleCriticalLineOriginConvergenceAndSynthesis.lean`**
    - `allScaleCriticalWeight`, `allScaleCriticalWeight_pos`,
      `allScaleCriticalWeight_le_two_div_sqrt_succ`, `allScaleCriticalWeight_le_archLevySinhWeight`:
      Canonical all-scale critical-line weight $\varpi_n = \sqrt{2}\,n(n^{-1/2} - (n+1)^{-1/2})$ and
      pointwise dominance by `archLevySinhWeight`.
    - `allScaleCriticalWeight_div_eq`, `sum_allScaleCriticalWeight_div_eq`,
      `sum_allScaleCriticalWeight_div_le_one`:
      Exact telescoping $O(n^{-3/2})$ origin-budget conservation across `[2, N + 2)`.
    - `nyquist_step_le_log_two`, `nyquist_cell_origin_integral_le_log_two_origin`,
      `origin_log_two_add_all_scale_tail_le_biScaleLevyEnergy`:
      Disjoint first-prime origin `(0, log 2]` plus all-scale tail `[log 2, log(N + 2)]` partition.
    - `allScaleCoerciveConstant`, `allScaleCoerciveConstant_pos`, `allScaleCoerciveConstant_mono`,
      `nyquist_cell_all_scale_signed_coercivity`, `global_all_scale_signed_coercivity`,
      `RealEvenPolarTestFn.unconditional_all_scale_signed_weil_lower_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_all_scale_signed_weil_lower_bound`,
      `RealEvenPolarTestFn.unconditional_coshMultiplier_all_scale_signed_coercivity`:
      Unconditional all-scale signed coercivity and Weil functional lower bounds across all dyadic
      shells simultaneously.

## Audit Status
- **Module Verification**: All 20 Pillars (`EulerMaclaurinLevyQuadratureAndSFreeCellBounds.lean`, `MultiShellOriginBudgetAndGlobalPrimeCollarSynthesis.lean`, `SignedWeilFunctionalCoercivityAndRHBridge.lean`, `AllScaleCriticalLineOriginConvergenceAndSynthesis.lean`, and Pillars I–XVI) compile to `.olean` with exit code `0` and zero warnings.
- **Axiom Audit**: `#print axioms` verified on all key theorems across Pillars I–XX; every declaration depends only on `[propext, Classical.choice, Quot.sound]`, with zero `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations.


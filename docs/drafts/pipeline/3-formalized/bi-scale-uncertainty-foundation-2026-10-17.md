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

21. **Pillar XXI — `formal/GaloisForLFunctions/BiScaleUncertainty/VonMangoldtWeilExplicitFormulaAndChebyshevBridge.lean`**
    - `vonMangoldtLogRatio`, `vonMangoldtLogRatio_nonneg`, `vonMangoldtLogRatio_le_one`,
      `vonMangoldtLogRatio_prime`, `vonMangoldtLogRatio_two`:
      Normalized von Mangoldt ratio $\theta_\Lambda(n) = \Lambda(n) / \log n \in [0, 1]$.
    - `allScaleVonMangoldtWeight`, `allScaleVonMangoldtWeight_nonneg`,
      `allScaleVonMangoldtWeight_le_allScaleCriticalWeight`,
      `allScaleVonMangoldtWeight_le_two_div_sqrt_succ`,
      `allScaleVonMangoldtWeight_prime_eq`, `allScaleVonMangoldtWeight_two_pos`,
      `allScaleVonMangoldtWeight_sub_sq_div_two_ge`:
      All-scale von Mangoldt critical-line weight $w_\Lambda(n) = \theta_\Lambda(n)\,\varpi_n$ and
      quadratic origin-regularization bound $\frac{1}{2} w_\Lambda(n) \le w_\Lambda(n) - \frac{w_\Lambda(n)^2}{2 \varpi_n}$.
    - `allScaleVonMangoldtCoerciveConstant`, `allScaleVonMangoldtCoerciveConstant_pos`,
      `allScaleVonMangoldtCoerciveConstant_mono`,
      `nyquist_cell_vonMangoldt_all_scale_signed_coercivity`,
      `global_vonMangoldt_all_scale_signed_coercivity`,
      `RealEvenPolarTestFn.unconditional_vonMangoldt_all_scale_signed_weil_lower_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_vonMangoldt_all_scale_signed_weil_lower_bound`,
      `RealEvenPolarTestFn.unconditional_coshMultiplier_vonMangoldt_all_scale_signed_coercivity`:
      Unconditional all-scale von Mangoldt signed coercivity and Weil functional lower bounds.
    - `RealEvenPolarTestFn.integral_Ioi_autocorr_mul_cosh_eq_zero`,
      `RealEvenPolarTestFn.unconditional_hyperbolic_lobe_conservation`,
      `RealEvenPolarTestFn.unconditional_weilArchRe_nonneg_iff`,
      `RealEvenPolarTestFn.vonMangoldt_prime_sum_eq_pairing_sub_polar_tail`:
      Unconditional polar vanishing, hyperbolic lobe conservation, and Chebyshev–polar truncation
      bridge on `RealEvenPolarTestFn`.

22. **Pillar XXII — `formal/GaloisForLFunctions/BiScaleUncertainty/ChebyshevWeilExplicitFormulaAndUnconditionalSynthesis.lean`**
    - `RealEvenPolarTestFn.toCompactlySupported`, `RealEvenPolarTestFn.coe_toCompactlySupported`:
      Canonical embedding of `RealEvenPolarTestFn` into `C_c(ℝ, ℝ)`.
    - `annular_levy_integral_le_biScaleLevyEnergy`,
      `RealEvenPolarTestFn.annular_levy_integral_le_weilArchRe`:
      Unconditional global annular Lévy domination by `biScaleLevyEnergy` and `weilArchRe`.
    - `RealEvenPolarTestFn.prime_sum_add_polar_tail_eq_pairing`,
      `RealEvenPolarTestFn.unconditional_chebyshev_packet_weil_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_chebyshev_packet_weil_bound`,
      `RealEvenPolarTestFn.unconditional_chebyshev_mass_weil_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_chebyshev_mass_weil_bound`,
      `RealEvenPolarTestFn.unconditional_joint_all_scale_and_chebyshev_weil_synthesis`:
      Unconditional cancellation-sensitive Chebyshev–Packet–Weil and Chebyshev–Mass–Weil
      explicit-formula bounds and joint all-scale synthesis on `RealEvenPolarTestFn` and
      `RealSmoothEvenPolarTestFn`.

23. **Pillar XXIII — `formal/GaloisForLFunctions/BiScaleUncertainty/WeilFullFunctionalAndPrimitiveHyperplaneBridge.lean`**
    - `RealEvenPolarTestFn.weilTest_neg_re_eq`,
      `RealEvenPolarTestFn.logValue_eq_two_mul_autocorr_div_sqrt`,
      `RealEvenPolarTestFn.logValue_eq_two_mul_weilTest_re_div_sqrt`,
      `RealEvenPolarTestFn.logValue_mul_vonMangoldt_eq_two_mul_primeWeight`:
      Exact `logValue` and `primeWeight` identities on `RealEvenPolarTestFn`.
    - `RealEvenPolarTestFn.poleWeightArchRe_eq_weilArchRe`,
      `RealEvenPolarTestFn.poleWeightArchRe_eq_gamma_add_biScaleLevyEnergy`,
      `RealEvenPolarTestFn.re_weilPoleWeightFunctional_eq_re_weilFullFunctional`:
      Pole-weight invariance of `poleWeightArchRe` and `weilPoleWeightFunctional` on
      `RealEvenPolarTestFn`.
    - `RealEvenPolarTestFn.supportRadius`, `RealEvenPolarTestFn.supportScale`,
      `RealEvenPolarTestFn.polar_tail_eq_zero_of_supportScale_le`,
      `RealEvenPolarTestFn.prime_sum_eq_pairing_of_supportScale_le`,
      `RealEvenPolarTestFn.linearCombination_vonMangoldt_logVector_eq_of_supportScale_le`:
      Canonical support scale and exact vanishing of both the polar tail and prime tail above
      `supportScale g`.
    - `RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_weilArchRe_sub_two_pairing`,
      `RealEvenPolarTestFn.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing`,
      `RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound`,
      `RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound`,
      `RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_all_scale_lower_bound`:
      100% unconditional full Weil functional identities and Chebyshev–Packet / all-scale bounds on
      `RealEvenPolarTestFn` and `RealSmoothEvenPolarTestFn`.

24. **Pillar XXIV — `formal/GaloisForLFunctions/BiScaleUncertainty/MultiNodeSignedCliqueWeilCoercivity.lean`**
    - `integral_finset_sum_shift_sq`, `autocorr_gram_quad_nonneg`,
      `autocorr_gram_quad_eq_diag_add_offDiag`:
      Exact multi-node shift Gram identity and diagonal-plus-off-diagonal decomposition.
    - `autocorr_multi_node_signed_collar_gram_ge`,
      `autocorr_multi_node_signed_collar_offDiag_ge`:
      Unconditional multi-node signed collar Gram and off-diagonal inequalities with zero blindness
      or orthogonality assumptions.
    - `dyadicCosetNode`, `dyadicCosetNode_sub_eq`, `autocorr_dyadicCosetNode_sub_eq`,
      `RealEvenPolarTestFn.unconditional_multi_node_signed_collar_offDiag_bound`,
      `RealEvenPolarTestFn.unconditional_dyadic_coset_multi_node_signed_collar_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_dyadic_coset_multi_node_signed_collar_bound`:
      Coset-invariance of dyadic node differences (`t_i - t_j = (i - j) log 2`), prime-`2`-power
      off-diagonal reduction, and unconditional multi-node dyadic-coset signed collar bounds on
      `RealEvenPolarTestFn` and `RealSmoothEvenPolarTestFn`.

25. **Pillar XXV — `formal/GaloisForLFunctions/BiScaleUncertainty/OddSectorAndPrimitiveHyperplaneBiScaleSynthesis.lean`**
    - `RealWeilTestFn`, `RealOddTestFn`, `RealHyperplaneGenerator`:
      Real-valued Weil test space (`{f : WeilTestFn // ∀ u, (f.1 u).im = 0}`), real odd test space,
      and primitive-hyperplane generator sum type (`RealOddTestFn ⊕ RealEvenPolarTestFn`).
    - `re_weilPoleTerm_ofReal_eq_cosh_sq_sub_sinh_sq`,
      `weilArchRe_ofReal_eq_pole_add_gamma_add_biScaleLevyEnergy`,
      `weilArchRe_ofReal_eq_cosh_sq_sub_sinh_sq_add_gamma_add_biScaleLevyEnergy`:
      Universal physical-space pole decomposition and archimedean identities for arbitrary real
      $f \in C^2_c(\mathbb{R})$.
    - `RealWeilTestFn.poleWeightArchRe_eq`,
      `RealWeilTestFn.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy`,
      `RealWeilTestFn.unconditional_vonMangoldt_all_scale_signed_poleWeightArchRe_zero_lower_bound`:
      Universal pole-weight archimedean decomposition and unconditional all-scale von Mangoldt
      signed lower bound across the entire real Weil test space.
    - `RealOddTestFn.integral_source_mul_cosh_eq_zero`,
      `RealOddTestFn.re_weilPoleTerm_eq_neg_two_mul_sinh_sq`,
      `RealOddTestFn.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy`,
      `RealOddTestFn.weilArchRe_add_two_mul_sinh_sq_eq_gamma_add_biScaleLevyEnergy`,
      `RealOddTestFn.unconditional_dyadic_signed_poleWeightArchRe_zero_lower_bound`,
      `RealOddTestFn.unconditional_vonMangoldt_all_scale_signed_poleWeightArchRe_zero_lower_bound`,
      `RealOddTestFn.unconditional_vonMangoldt_all_scale_signed_weilArchRe_sinh_lower_bound`,
      `RealOddTestFn.unconditional_dyadic_coset_multi_node_signed_collar_bound`:
      Exact odd-sector Sinh-Capacity Weil identity at $\beta = 1$ and unconditional odd-sector
      coercivity bounds.
    - `RealHyperplaneGenerator.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy`,
      `RealHyperplaneGenerator.unconditional_vonMangoldt_all_scale_signed_lower_bound`:
      Unified primitive-hyperplane generator coercivity across both odd and even-polar generators.

26. **Pillar XXVI — `formal/GaloisForLFunctions/BiScaleUncertainty/IntegratedMultiNodeDyadicCosetWeilCoercivity.lean`**
    - `integral_multi_node_signed_collar_offDiag_ge`,
      `origin_collar_integral_le_biScaleLevyEnergy`,
      `shifted_collar_integral_le_biScaleLevyEnergy`,
      `dyadic_coset_integrated_multi_node_signed_collar_ge`:
      Unconditional integrated multi-node signed collar off-diagonal inequality and origin/shifted
      collar Lévy bounds.
    - `RealEvenPolarTestFn.unconditional_dyadic_coset_integrated_multi_node_signed_collar_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_dyadic_coset_integrated_multi_node_signed_collar_bound`,
      `RealWeilTestFn.unconditional_dyadic_coset_integrated_multi_node_signed_collar_bound`,
      `RealOddTestFn.unconditional_dyadic_coset_integrated_multi_node_signed_collar_bound`:
      Unconditional integrated multi-node dyadic-coset signed collar bounds across all explicit-formula
      test spaces.

27. **Pillar XXVII — `formal/GaloisForLFunctions/BiScaleUncertainty/AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis.lean`**
    - `four_mul_integral_Ioi_autocorr_mul_cosh_eq_re_weilPoleTerm`,
      `two_mul_integral_Ioi_polarDensity_autocorr_eq_re_weilPoleTerm`:
      Universal identity between the continuum polar counterterm of `SignedPrimePolar.pairing` and
      the real part of `weilPoleTerm` for arbitrary real $f \in C^2_c(\mathbb{R})$.
    - `RealWeilTestFn.two_mul_prime_sum_add_polar_tail_eq_two_pairing_add_pole`,
      `RealWeilTestFn.linearCombination_vonMangoldt_logVector_eq_two_pairing_add_pole`,
      `RealWeilTestFn.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing`,
      `RealWeilTestFn.re_weilFullFunctional_vonMangoldt_eq_poleWeightArchRe_zero_sub_two_pairing`:
      Universal Pole-to-Chebyshev Absorption Theorem on `RealWeilTestFn` at $\beta = 1$ with zero
      parity or polar-vanishing hypotheses.
    - `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound`,
      `RealOddTestFn.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing`,
      `RealOddTestFn.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound`:
      Unconditional full Weil functional Chebyshev–Packet bounds across all parities.

28. **Pillar XXVIII — `formal/GaloisForLFunctions/BiScaleUncertainty/HyperbolicGaugeMeanSquareChebyshevWeilSynthesis.lean`**
    - `discreteChebyshevCellSum`, `smoothGaugeBound`, `discreteCellGaugeBound`,
      `integral_normalizedLogError_sq_cutoff_eq_chebyshev_mean_square`,
      `integral_normalizedLogError_sq_cutoff_eq_sum_center_add_floor`,
      `sum_center_sq_le_integral_cutoff_le`,
      `packetEnergy_le_smoothGaugeBound`, `packetEnergy_le_discreteCellGaugeBound`:
      Unconditional cutoff-level Nyquist-cell quadrature and hyperbolic-gauge mean-square Chebyshev
      packet bounds for every $N : \mathbb{N}$.
    - `RealWeilTestFn.contDiff_one_source`, `RealWeilTestFn.signedSource_eq_gauge`,
      `RealWeilTestFn.packetEnergy_le_smoothGaugeBound`,
      `RealWeilTestFn.packetEnergy_le_discreteCellGaugeBound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_smoothGauge_bound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_smoothGauge_lower_bound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_roughGauge_lower_bound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_correlationGauge_lower_bound`:
      100% unconditional full Weil functional lower bounds controlled by the continuous mean-square
      Chebyshev gauge bound, the discrete Nyquist-cell centered Chebyshev sum, the derivative-free
      rough collar gauge bound, and the correlation-only collar gauge bound.
    - `RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_smoothGauge_lower_bound`,
      `RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound`,
      `RealOddTestFn.unconditional_weilFullFunctional_vonMangoldt_smoothGauge_lower_bound`,
      `RealOddTestFn.unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound`,
      `RealHyperplaneGenerator.unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound`:
      Unconditional lifts across `RealEvenPolarTestFn`, `RealSmoothEvenPolarTestFn`,
      `RealOddTestFn`, and `RealHyperplaneGenerator`.
    - `integral_deriv_mul_self_eq_zero`, `integral_gaugeDerivative_sq`,
      `RealWeilTestFn.integral_gaugeDerivative_sq`:
      Exact $L^2$ orthogonality $\int f' f = 0$ and hyperbolic-gauge derivative energy decomposition
      $\int (f' - f/2)^2 = \int (f')^2 + \frac{1}{4} h_f(0)$.

29. **Pillar XXIX — `formal/GaloisForLFunctions/BiScaleUncertainty/ExplicitNyquistPolarAndChebyshevFactorialProducer.lean`**
    - `nyquistPolarConstant`, `nyquistPolarConstant_eq_sqrt_avg`,
      `sqrt_succ_sub_sqrt_le`, `nyquistPolarConstant_succ_sub_le`,
      `nyquist_cell_cosh_sub_polarConstant_bounds`,
      `nyquist_cell_polar_producer_l2_error_le`:
      Explicit Nyquist-cell polar producer $\operatorname{nyquistPolarConstant}(n) = \cosh((\log n)/2) = \frac{\sqrt{n} + 1/\sqrt{n}}{2}$,
      pointwise Nyquist-cell drift bound $0 \le \cosh(x/2) - \operatorname{nyquistPolarConstant}(n) \le \frac{1}{4\sqrt{n}}$,
      and unconditional $L^2$ approximation bound $\int_{\log n}^{\log(n+1)} (\cosh(x/2) - \operatorname{nyquistPolarConstant}(n))^2\,dx \le \frac{1}{16 n^2}$.
    - `nyquist_cell_producer_consumer_residual_sq_le`,
      `dyadic_window_polar_producer_l2_error_sum_le`:
      Instantiated Nyquist-cell Producer–Consumer Residual Theorem (eliminating the uninstantiated
      producer weight $W$ from Pillar XII) and unconditional $O(1/N)$ dyadic-window producer $L^2$
      error bound $\le \frac{1}{16 N}$.
    - `stirlingResidual`, `floorSummatory_chebyshevPsi_eq_main_add_stirlingResidual`,
      `stirlingResidual_bounds`:
      Unconditional $O(\log k)$ Stirling residual sandwich $1 \le T(k) - (k \log k - k) \le \log(k+1) + 1$
      for $T(k) = \operatorname{floorSummatory}\;\operatorname{chebyshevPsi}\;k$.
    - `chebyshevAlternatingProducer`, `chebyshevAlternatingProducer_eq_linear_add_stirling`,
      `abs_chebyshevAlternatingProducer_sub_linear_le`,
      `floorSummatory_chebyshevPsi_eq_sum_vonMangoldt_mul_div`,
      `chebyshevPsi_two_mul_sub_le_alternatingProducer`,
      `chebyshevPsi_two_mul_sub_le_linear_add_log`,
      `chebyshevAlternatingProducer_le_chebyshevPsi_two_mul`,
      `linear_sub_log_le_chebyshevPsi_two_mul`,
      `chebyshevBiNullProducer`, `chebyshevBiNullProducer_eq_alternating_diff`,
      `chebyshevBiNullProducer_eq_stirling_second_diff`,
      `abs_chebyshevBiNullProducer_le`:
      Explicit first-order Chebyshev–Nyman–Beurling alternating producer $T(2N) - 2T(N)$ with exact
      double-pole cancellation, unconditional $O(\log N)$ linear tracking bound
      $|T(2N) - 2T(N) - (2\log 2)N| \le 2\log(2N+1) + 1$, two-sided Chebyshev prime-generating
      sandwich $\psi(2N) - \psi(N) \le T(2N) - 2T(N) \le \psi(2N)$, and second-order bi-null
      Chebyshev producer $T(4N) - 4T(2N) + 4T(N)$ cancelling both $N \log N$ and $N$ poles
      identically with unconditional bound $|T(4N) - 4T(2N) + 4T(N)| \le 5\log(4N+1) + 1$.

30. **Pillar XXX — `formal/GaloisForLFunctions/BiScaleUncertainty/ChebyshevCellAndArchimedeanWeilProducer.lean`**
    - `generalChebyshevStencilProducer`, `floorSummatory_chebyshevPsi_mul_eq`,
      `generalChebyshevStencilProducer_eq`, `abs_generalBiNullChebyshevProducer_le`,
      `coprimeTwoThreeChebyshevProducer`, `coprimeTwoThreeChebyshevProducer_eq_alternating_diff`,
      `coprimeTwoThreeChebyshevProducer_eq_stirling_comb`,
      `abs_coprimeTwoThreeChebyshevProducer_le`:
      Exact pole–slope–Stirling decomposition for general finite dilation stencils $\sum_{a \in s} c_a T(aN)$,
      general $O(\log N)$ bi-null producer bound, and the explicit coprime $(2, 3)$
      Chebyshev–Nyman–Beurling producer $T(6N) - 2T(3N) - 3T(2N) + 6T(N)$ with bound
      $|T(6N) - 2T(3N) - 3T(2N) + 6T(N)| \le 12\log(6N+1) + 2$.
    - `chebyshevProducerSlope`, `abs_chebyshev_psi_sub_self_le`,
      `abs_logError_le_exp`, `abs_normalizedLogError_le_exp_half`,
      `normalizedLogError_cutoff_sq_le`, `abs_chebyshev_psi_sub_cellCenter_le`,
      `nyquist_cell_chebyshev_term_le`, `discreteChebyshevCellSum_le`,
      `integral_normalizedLogError_sq_cutoff_le`:
      Pointwise and Nyquist-cell Chebyshev producer bounds:
      $|\psi(n) - m_n| \le (\log 4 + 3)n$, $(\psi(n) - m_n)^2 / (n(n+1)) \le (\log 4 + 3)^2$, and
      $\operatorname{discreteChebyshevCellSum}(N) \le (\log 4 + 3)^2 (N + 1)$.
    - `archimedeanPacketProducerBound`,
      `discreteCellGaugeBound_le_archimedeanPacketProducerBound`,
      `packetEnergy_le_archimedeanPacketProducerBound`,
      `two_mul_abs_pairing_le_exp_add_packetEnergy`,
      `two_mul_abs_pairing_le_archimedeanPacketProducerBound`:
      100% prime-free archimedean packet and pairing producer bounds eliminating `chebyshevWork`,
      `normalizedLogError`, `discreteChebyshevCellSum`, and `Chebyshev.psi`.
    - `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_bound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound`,
      `RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound`,
      `RealSmoothEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound`,
      `RealOddTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound`,
      `RealHyperplaneGenerator.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound`:
      Prime-free archimedean full Weil functional lower bounds across all explicit-formula
      test spaces.

31. **Pillar XXXI — `formal/GaloisForLFunctions/BiScaleUncertainty/LaplaceEnergyAndRoughCollarWeilProducer.lean`**
    - `chebyshevPsi_one_eq_zero`, `sum_dyadic_chebyshevPsi_diff_eq`,
      `dyadicCumulativeChebyshevProducer`,
      `chebyshevPsi_two_pow_le_dyadicCumulativeChebyshevProducer`,
      `sum_range_two_pow_nat_cast`, `dyadicCumulativeChebyshevProducer_le`,
      `chebyshevPsi_two_pow_le_linear_add_log`:
      All-scale telescoping dyadic Chebyshev factorial producer
      $\operatorname{dyadicCumulativeChebyshevProducer}(K) = \sum_{k=0}^{K-1} (T(2^{k+1}) - 2T(2^k))$
      and Stirling-only dyadic Chebyshev upper bound
      $\psi(2^K) \le (2\log 2)(2^K - 1) + K(2\log(2^K + 1) + 1)$.
    - `laplaceEnergyProducerBound`, `laplaceEnergy_le_laplaceEnergyProducerBound`,
      `normalizedLogError_cutoff_sq_le_laplaceEnergy`,
      `packetEnergy_le_laplaceEnergy_gauge`:
      Prime-free archimedean producer bound on `laplaceEnergy N` and direct Laplace
      Gram energy control of `packetEnergy f N`.
    - `primeWeight_le_vonMangoldt`, `sum_primeWeight_le_chebyshev_psi`,
      `integral_polarDensity_cutoff_eq`, `massProducerBound`,
      `mass_le_massProducerBound`, `mass_sq_le_massProducerBound_sq`:
      Prime-free archimedean producer bound on `SignedPrimePolar.mass N`.
    - `archimedeanCollarPacketProducerBound`, `archimedeanCorrelationGaugeProducerBound`,
      `archimedeanCollarTrialProducerBound`,
      `packetEnergy_le_archimedeanCorrelationGaugeProducerBound`,
      `packetEnergy_le_archimedeanCollarTrialProducerBound`,
      `two_mul_abs_pairing_le_archimedeanCorrelationGaugeProducerBound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_bound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound`,
      `RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound`,
      `RealOddTestFn.unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound`,
      `RealHyperplaneGenerator.unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound`:
      Derivative-free, correlation-only, 100% prime-free archimedean packet, pairing, and full Weil
      functional bounds across all explicit-formula test spaces.

32. **Pillar XXXII — `formal/GaloisForLFunctions/BiScaleUncertainty/CoprimeFactorialLiftAndSpectralLaplaceProducer.lean`**
    - `coprimeHarmonicCorrection`, `coprimeHarmonicCorrection_eq_pairs`,
      `coprimeHarmonicCorrection_bounds`:
      $[0, 3]$ bound on the coprime $(2, 3)$ harmonic second difference
      $6N(H_{6N} - H_{3N} - H_{2N} + H_N)$.
    - `factorialCoprimeTwoThree`, `factorialCoprimeTwoThree_zero`,
      `factorialCoprimeTwoThree_top`, `factorialCoprimeTwoThree_ne_autocorr`,
      `factorialCoprimeTwoThree_admissible`,
      `fullPairing_factorialCoprimeTwoThree_eq`,
      `abs_fullPairing_factorialCoprimeTwoThree_le`,
      `factorialCoprimeTwoThree_producer`:
      Explicit coprime $(2, 3)$ real-ratio factorial-lift producer for `fullPairing` with exact
      evaluation $(2\,\operatorname{coprimeTwoThreeChebyshevProducer}(N) - \operatorname{coprimeHarmonicCorrection}(N))/\sqrt{N}$
      and $O(\log N / \sqrt{N})$ bound $\le (24\log(6N+1) + 7)/\sqrt{N}$.
    - `norm_fourierPairing_le_massProducerBound`,
      `spectral_fourierPairing_integral_le_laplaceEnergyProducerBound`,
      `packetEnergy_le_spectral_fourierPairing`,
      `packetEnergy_le_gauge_sq_mul_laplaceEnergyProducerBound`,
      `collar_packetEnergy_le_budget_mul_laplaceEnergy`,
      `collar_packetEnergy_le_budget_mul_laplaceEnergyProducerBound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_bound`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound`,
      `RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound`,
      `RealOddTestFn.unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound`,
      `RealHyperplaneGenerator.unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound`:
      Prime-free critical-line spectral Laplace producer bounds and boundary-free
      multiplicative full Weil functional lower bounds across all explicit-formula test spaces.

33. **Pillar XXXIII — `formal/GaloisForLFunctions/BiScaleUncertainty/ChebyshevHeadAndShearCellProducer.lean`**
    - `chebyshev_psi_natCast_eq_chebyshevPsi`, `chebyshevPsiSeq_eq_chebyshevPsi`,
      `dyadicChebyshevDiffSeq_two_mul_eq`,
      `sub_alternatingProducer_le_dyadicChebyshevDiffSeq_two_mul`,
      `dyadicChebyshevDiffSeq_two_mul_le_two_mul_sub_alternatingProducer`,
      `stirling_lower_bound_dyadicChebyshevDiffSeq_two_mul`,
      `dyadicChebyshevDiffSeq_two_mul_le_stirling_upper_bound`,
      `dyadicChebyshevDiffSeq_two_mul_two_pow_le_cumulative_sub_alternating`,
      `dyadicChebyshevDiffSeq_two_mul_two_pow_le_stirling_linear_add_log`:
      Exact bridge $\operatorname{Chebyshev.psi}(m) = \operatorname{RHTower.chebyshevPsi}(m)$,
      two-sided Stirling producer sandwich for $\operatorname{dyadicChebyshevDiffSeq}(2m)$, and
      pure-Stirling upper bound at dyadic scales $2 \cdot 2^K$.
    - `abs_chebyshevErrorSeq_le`, `chebyshevErrorSeq_sq_div_cell_le`,
      `integerCenteredChebyshevCellSum_le`, `vonMangoldt_shear_harmonic_sum_le`,
      `archimedeanIntegerCenteredGaugeProducerBound`,
      `integerCenteredGaugeBound_le_archimedeanProducer`,
      `RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanIntegerCenteredProducer_lower_bound`:
      Linear producer bound $\operatorname{integerCenteredChebyshevCellSum}(N) \le (\log 4 + 3)^2 (N + 1)$,
      harmonic bilinear von Mangoldt shear sum bound, and prime-free integer-centered gauge producer.
    - `abs_two_mul_chebyshev_psi_half_sub_le`, `sq_two_mul_chebyshev_psi_half_sub_le`,
      `integrableOn_inv_sq_Ioc`, `integral_inv_sq_Ioc`,
      `integral_wall_one_chebyshev_head_le`,
      `logMobiusFermiErrorEnergy_le_tail_add_head_producer`:
      Closed-form bound $\int_{1/(N+1)}^1 (2\psi(1/(2t)) - \psi(1/t))^2\,dt \le (\log 4 + 4)^2 N$
      and resulting head producer bound on `logMobiusFermiErrorEnergy N`.
    - `coprimeFactorialCollar`, `smoothFactorialCoprimeTwoThree`,
      `continuousCoprimeFactorialProducer`,
      `smoothFactorialCoprimeTwoThree_at_log`,
      `smoothFactorialCoprimeTwoThree_admissible`,
      `fullPairing_smoothFactorialCoprimeTwoThree_correction`,
      `fullPairing_smoothFactorialCoprimeTwoThree_eq`,
      `abs_fullPairing_smoothFactorialCoprimeTwoThree_le`,
      `continuousCoprimeFactorialProducer_zero`,
      `continuousCoprimeFactorialProducer_top`,
      `continuousCoprimeFactorialProducer_ne_autocorr`:
      Compactly supported continuous coprime $(2, 3)$ factorial producer in $C_c(\mathbb{R}, \mathbb{R})$
      with exact collar correction and $O(\log N / \sqrt{N})$ pairing bound.

34. **Pillar XXXIV — `formal/GaloisForLFunctions/BiScaleUncertainty/SawtoothPhaseCancellationAndBandSpectralProducer.lean`**
    - `moebiusLogHarmonicSum`,
      `chebyshevPsiSeq_eq_common_cutoff_harmonic_sub_fractSum`,
      `chebyshevErrorSeq_eq_common_cutoff_harmonic_drift_sub_fractSum`,
      `vonMangoldt_succ_eq_common_cutoff_harmonic_sub_addDiff_fractSum`,
      `vonMangoldt_succ_sub_one_eq_common_cutoff_drift_sub_addDiff_fractSum`,
      `dyadicChebyshevDiffSeq_two_mul_eq_fractSum_diff`:
      Common-cutoff harmonic-drift cancellation and pure sawtooth-phase representation
      $\operatorname{dyadicChebyshevDiffSeq}(2m) = \Phi_{\mathrm{fract}}(2m+k, 2m) - 2\,\Phi_{\mathrm{fract}}(2m+k, m)$.
    - `abs_vonMangoldtDivisorWeight_le_log`, `fractDivSeq_bounds`,
      `abs_weightedFractSumSeq_vonMangoldt_le_floorSummatory`,
      `abs_weightedFractSumSeq_vonMangoldt_le_stirling`,
      `abs_dyadic_sawtooth_phase_diff_le`,
      `dyadic_sawtooth_phase_diff_stirling_sandwich`,
      `sum_weightedFractSumSeq_eq_harmonic_mul_sum_sub_sum_chebyshevPsi`,
      `sum_weightedFractSumSeq_div_eq_harmonic_mul_divisor_sub_floorSummatory`:
      Log-factorial bound on individual sawtooth sums, $\log$-free linear bound and Stirling
      sandwich on the dyadic sawtooth phase difference, and exact cumulative identities.
    - `bandRemainderProducer`, `bandRemainderProducer_nonneg`,
      `band_spectralDensity_integral_le_laplaceEnergyProducerBound`,
      `packetEnergy_le_band_spectralDensity_add_remainder`,
      `collar_packetEnergy_le_band_spectralDensity_add_remainder`,
      `RealWeilTestFn.weilFullFunctional_vonMangoldt_bandSpectral_bound`,
      `RealWeilTestFn.weilFullFunctional_vonMangoldt_bandSpectral_lower_bound`,
      `RealEvenPolarTestFn.weilFullFunctional_vonMangoldt_bandSpectral_lower_bound`,
      `RealOddTestFn.weilFullFunctional_vonMangoldt_bandSpectral_lower_bound`,
      `RealHyperplaneGenerator.weilFullFunctional_vonMangoldt_bandSpectral_lower_bound`:
      Band-limited critical-line spectral density producer bounds on `packetEnergy`,
      `collarSource`, and `weilFullFunctional Λ` across all explicit-formula test spaces.

35. **Pillar XXXV — `formal/GaloisForLFunctions/BiScaleUncertainty/DyadicRenewalStirlingAndLogMobiusTotalEnergyProducer.lean`**
    - `norm_logMobiusFermiApprox_coeff_le_one`, `norm_logMobiusFermiApprox_le_three_mul`,
      `normSq_dyadicHaar_sub_logMobiusFermiApprox_le`,
      `integral_normSq_dyadicHaar_sub_logMobiusFermiApprox_tail_le`,
      `logMobiusTotalEnergyProducer`,
      `logMobiusFermiErrorEnergy_le_total_producer`,
      `logMobiusFermiErrorEnergy_succ_succ_le_total_producer`,
      `L2FermiWitness.integral_logMobiusFermiApprox_mul_conj_eq_zero`,
      `L2FermiWitness.norm_sq_dyadicHaar_pairing_le_logMobiusTotalEnergyProducer`:
      Closed-form tail energy bound $\int_0^{1/(N+1)} \|\mathrm{dyadicHaar}(t) - A_N(t)\|^2\,dt \le \frac{(1+3N)^2}{N+1}$,
      total energy producer bound $\operatorname{logMobiusFermiErrorEnergy}(N) \le \frac{(1+3N)^2}{N+1} + \frac{(\log 4 + 4)^2 N}{(\log N)^2}$,
      exact orthogonality of every $L^2$ Fermi witness to `logMobiusFermiApprox N`, and unconditional
      dyadic-Haar pairing bound.
    - `chebyshev_psi_two_pow_eq`, `chebyshev_psi_two_pow_succ_eq`,
      `chebyshev_psi_two_pow_succ_sub_bounds`, `chebyshev_psi_two_pow_succ_sub_le_stirling`,
      `chainInput_log_two_alternating_sandwich`, `chainInput_log_two_le_stirling`,
      `dyadicRenewalStirlingInputProducer`, `abs_chainInput_log_two_le_producer`,
      `sum_chainState_log_two_sq_le_stirlingProducer`,
      `integral_sq_causalResponse_le_dyadic_stirlingProducer`,
      `norm_boundaryTransform_le_producer`:
      Hypothesis-free Stirling producer bounds on the dyadic renewal chain (`chainInput (log 2) k`,
      `chainState (log 2) K`, `causalResponse N`, and `boundaryTransform N`).
    - `abs_moebiusDivisorWeight_le_one`, `sum_abs_moebiusDivisorWeight_le`,
      `sievedDivisorMeanSquare_moebius_le_selberg_diagonal_add_sq`,
      `sum_abs_vonMangoldtDivisorWeight_le_floorSummatory`,
      `sievedDivisorMeanSquare_vonMangoldt_le_selberg_diagonal_add_floorSummatory_sq`,
      `sum_divisors_vonMangoldtDivisorWeight_succ_eq`,
      `tailSievedDivisorMeanSquare_vonMangoldt_le_selberg_diagonal_add_floorSummatory_sq`:
      Explicit Möbius and von Mangoldt instantiation of the Selberg sieve tail quadratic form and
      exact cancellation of all smooth divisor sums $1 \le n \le N$ under `vonMangoldtDivisorWeight`.

36. **Pillar XXXVI — `formal/GaloisForLFunctions/BiScaleUncertainty/FoldFreeLogMobiusAndPlancherelCausalProducer.lean`**
    - `logMobiusHarmonicShadow`, `foldFreeLogMobiusFermiApprox`, `foldFreeLogMobiusErrorEnergy`,
      `integral_logMobiusFermiApprox_mul_canonicalSelfSimilar`,
      `logMobiusHarmonicShadow_eq_finiteHarmonicSum_add_moebiusLogHarmonicSum`,
      `integral_foldFreeLogMobiusFermiApprox_mul_canonicalSelfSimilar`,
      `logMobiusFermiErrorEnergy_eq_foldFree_add_shadow_sq`,
      `foldFreeLogMobiusErrorEnergy_le_producer_sub_shadow`,
      `logMobiusHarmonicShadow_sq_le_two_mul_producer`,
      `L2FermiWitness.integral_foldFreeLogMobiusFermiApprox_mul_conj_eq_zero`,
      `L2FermiWitness.norm_sq_dyadicHaar_pairing_le_foldFree_producer`:
      Exact inner product $\langle \operatorname{logMobiusFermiApprox}(N), t^{-1/2}\rangle = \operatorname{logMobiusHarmonicShadow}(N)$,
      fold-free orthogonal projection, and Pythagoras identity
      $\operatorname{logMobiusFermiErrorEnergy}(N) = \operatorname{foldFreeLogMobiusErrorEnergy}(N) + \tfrac{1}{2}\operatorname{logMobiusHarmonicShadow}(N)^2$.
    - `integral_polar_sourceFactorialCausal`, `fullPairing_sourceFactorialCausal_eq`,
      `abs_fullPairing_sourceFactorialCausal_le`, `abs_fullPairing_causalFactorialProducer_le`:
      Exact full prime-polar pairing identity
      $\operatorname{fullPairing}(\operatorname{sourceFactorialCausal}\,N) = \frac{2\,\operatorname{chebyshevBiNullProducer}(N) - c_N\,\operatorname{harmonicCorrection}(N)}{\sqrt{N}}$
      and unconditional $O(\log N / \sqrt{N})$ bound for `causalFactorialProducer n`.
    - `integral_fourier_mul_spectralDensity_le_laplaceProducer`:
      Plancherel–Laplace spectral producer bridge bounding $\int \|\mathcal{F}f(\xi)\|^2 (\tfrac{1}{4} + 4\pi^2\xi^2) S_N(\xi)\,d\xi$
      by `laplaceEnergyProducerBound N`.
    - `franelGramEntry_eq_gcd_div_lcm`, `one_div_twelve_lcm_le_franelGramEntry`,
      `franelGramEntry_eq_one_div_twelve_lcm_of_coprime`:
      Exact Franel–Selberg GCD–LCM Gram law $\operatorname{franelGramEntry}(a, b) = \frac{\gcd(a+1,b+1)}{12\,\operatorname{lcm}(a+1,b+1)}$
      and pointwise dominance over the smooth Selberg LCM kernel.

37. **Pillar XXXVII — `formal/GaloisForLFunctions/BiScaleUncertainty/DivisorAverageChebyshevAndDyadicBlockVarianceProducer.lean`**
    - `log_add_one_le_realHarmonic`, `realHarmonic_le_one_add_log`, `realHarmonic_bounds`,
      `log_le_realHarmonic`, `sum_logError_log_ratio_bounds`,
      `sum_sqrt_mul_normalizedLogError_bounds`, `mul_log_add_one_sub_log_le_one`,
      `pairing_factorialLift_bounds`, `fullPairing_factorialLift_bounds`:
      Two-sided logarithmic bounds $\log(K+1) \le H_K \le 1 + \log K$ and exact $K\log K$-free
      linear channels $-2K \le \sum_{j=1}^K \operatorname{logError}(\log(K/j)) \le -K + \log(K+1) + 1$
      and $-2K \le \operatorname{pairing}_N(\operatorname{factorialLift}\,K) \le -K + 2\log(K+1) + 2$.
    - `quantitativeGramCoefficient_factorialSourcePlus_allocation_error`,
      `quantitativeGramCoefficient_factorialSourceMinus_allocation_error`,
      `quantitativeGramCoefficient_factorialSourcePlus_limiting_error`,
      `quantitativeGram_and_roughCollar_producer_package`:
      Instantiation of the monotone quantitative Gram producer on `factorialSourcePlus m` and
      `factorialSourceMinus m` with $46\sqrt{m+1}(r_0+1)/(n+1)$ allocation error and joint
      rough-collar producer package.
    - `finiteBlockVariance_two`, `integerBlockVariance_two`, `integerBlockSum_two`,
      `summable_dyadicHaar_detail_sq`, `dyadicHaar_detail_tsum_eq`,
      `dyadicHaar_energy_conservation`, `integerBlockSum_two_energy_eq_iff`:
      Closed-form dyadic Haar block variance $(w(2j+1) - w(2j))^2$, exact wavelet energy
      conservation $\sum_j (w(2j+1) - w(2j))^2 + \|\operatorname{integerBlockSum}\,2\,w\|^2 = 2\|w\|^2$,
      and pairwise constancy characterization.
    - `nyquistWeightCellMass_half_zero_le`, `nyquistWeightCellMass_half_one_le_rpow`,
      `rpow_neg_five_halves_le_inv_sq`, `nyquistWeightCellMass_half_one_le_inv_sq`,
      `sum_nyquistWeightCellMass_half_one_le`:
      Critical-line ($\beta = 1/2$) Nyquist Taylor cell mass producer bounds at orders $m = 0$ and
      $m = 1$, plus cumulative finite-horizon inverse-square bound.

## Audit Status
- **Module Verification**: All 37 Pillars (`DivisorAverageChebyshevAndDyadicBlockVarianceProducer.lean`, `FoldFreeLogMobiusAndPlancherelCausalProducer.lean`, `DyadicRenewalStirlingAndLogMobiusTotalEnergyProducer.lean`, `SawtoothPhaseCancellationAndBandSpectralProducer.lean`, `ChebyshevHeadAndShearCellProducer.lean`, `CoprimeFactorialLiftAndSpectralLaplaceProducer.lean`, `LaplaceEnergyAndRoughCollarWeilProducer.lean`, `ChebyshevCellAndArchimedeanWeilProducer.lean`, `ExplicitNyquistPolarAndChebyshevFactorialProducer.lean`, `HyperbolicGaugeMeanSquareChebyshevWeilSynthesis.lean`, `AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis.lean`, `IntegratedMultiNodeDyadicCosetWeilCoercivity.lean`, `OddSectorAndPrimitiveHyperplaneBiScaleSynthesis.lean`, `MultiNodeSignedCliqueWeilCoercivity.lean`, `WeilFullFunctionalAndPrimitiveHyperplaneBridge.lean`, `ChebyshevWeilExplicitFormulaAndUnconditionalSynthesis.lean`, `VonMangoldtWeilExplicitFormulaAndChebyshevBridge.lean`, `AllScaleCriticalLineOriginConvergenceAndSynthesis.lean`, `SignedWeilFunctionalCoercivityAndRHBridge.lean`, `MultiShellOriginBudgetAndGlobalPrimeCollarSynthesis.lean`, `EulerMaclaurinLevyQuadratureAndSFreeCellBounds.lean`, and Pillars I–XVI) compile to `.olean` with exit code `0` and zero warnings.
- **Axiom Audit**: `#print axioms` verified on all key theorems across Pillars I–XXXVII; every declaration depends only on `[propext, Classical.choice, Quot.sound]`, with zero `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations.


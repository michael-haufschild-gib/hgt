# Resolution of the Deuring–Heilbronn question: orthogonal factorization of `AAL`, co-moving remainder phase transition, and two-scale integer-norm Euler obstruction

- **ID:** elt-deuring-heilbronn-and-two-scale-euler-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0911/obstacles-summary.md` §3
- **Statement:** Unconditionally: (1) on `ZeroConfig` and `zetaZeroConfig`, `AAL` factors orthogonally as `LinearAbscissaLaw ∧ ExtremeDeuringHeilbronn` (`↔ LinearAbscissaLaw ∧ AsymptoticDeuringHeilbronn`), with `ExtremeDeuringHeilbronn ↔ (AAL ↔ (FiniteOffLine → RH))`; (2) for every `1/2 < θ ≤ θ₂ < β < 2/3` and `γ > 0`, there exists a convergent integer-norm Euler product `∏_k (1 − q_k^{-s})^{-1} = ∑_n a_n n^{-s}` (`q_k ≥ 2`, `a_n ∈ ℕ`, `(1/N)∑_{n<N} a_n → A > 0`) continuing holomorphically and zero-free across `Re s = 1/2` to `{Re s > 1/3, s ≠ 1}` whose zeros there are `{β ± iγ} ∪ {θ_n ± iω_n : n ∈ ℕ}` (`θ_0 = θ₂`, `θ_{n+1} = θ`, `ω_n > γ`, `ω_n → ∞`), realizing `(Θ, Θ₂, Θ∞) = (β, θ₂, θ)` and refuting extreme, asymptotic, and sub-`Θ₂` graded Deuring–Heilbronn on positive Euler products; (3) for `ζ(s)`, every pair of nontrivial zeros obeys an explicit multiplicity-exact 5-point repulsion inequality alongside `1/58 < (1 − Re ρ₁) log(|Im ρ₁| · |Im ρ₂|)` (excluding the Siegel regime), while in the `exp(−at)` Gaussian prime current a co-moving remainder zero at `β_r + it` (`σ < β_r < β`) beats the supercritical top layer on the nonempty speed window `π/(2(β − σ)) < a < π/(2(β − β_r))` and is masked only for `a > π/(2(β − β_r))`.

## Lean
- Module `ExceptionalLayerTheory/TheDeuringHeilbronnQuestionForZeta.lean` (namespace `GaloisForLFunctions.ExceptionalLayerTheory`):
  `AsymptoticDeuringHeilbronn`, `ExtremeDeuringHeilbronn`, `asymptoticDeuringHeilbronn_tfae`, `extremeDeuringHeilbronn_tfae`, `abscissaLaw_orthogonal_factorization_tfae`, `harmonicConfig_asymptotic_not_extreme_deuringHeilbronn`, `not_isAsymptotic_deuringHeilbronn`, `not_isLocalBelow_deuringHeilbronn`, `ZetaAsymptoticDeuringHeilbronn`, `ZetaExtremeDeuringHeilbronn`, `zetaAsymptoticDeuringHeilbronn_tfae`, `zetaExtremeDeuringHeilbronn_tfae`, `asymptoticAbscissaLaw_orthogonal_factorization_tfae`, `zetaLinearAbscissaLaw_iff_b13_of_extremeDeuringHeilbronn`, `riemannHypothesis_iff_zerosApproachLine_and_b13_of_extremeDeuringHeilbronn`, `riemannHypothesis_tfae_of_extremeDeuringHeilbronn_and_b13`, `zetaZeroAbscissa_bound_of_graded_repulsion_and_linearAbscissaLawAt`, `symmetricShift_xi_violates_extremeDeuringHeilbronn_of_not_aal`, `oneOff_euler_product_extremeDeuringHeilbronn_not_linear`, `twoScale_euler_product_linear_not_asymptoticDeuringHeilbronn`, `no_sub_ceiling_graded_deuring_heilbronn_on_integer_norm_euler_products`.
- Module `ArithmeticPositiveDuality/ATwoScaleIntegerNormOneOff.lean` (namespace `GaloisForLFunctions.ArithmeticPositiveDuality.TwoScaleIntegerNormOneOff`):
  `frullaniCutoffFactor`, `frullaniCutoffLog`, `differentiable_frullaniCutoffFactor`, `frullaniCutoffFactor_eq_zero_iff`, `frullaniCutoffLog_eq_neg_integral_of_re_pos`, `norm_frullaniCutoffLog_le_of_im_ne_zero`, `TwoScaleSpec`, `TwoScaleSpec.continuous_wRem`, `TwoScaleSpec.abs_wRem_le`, `TwoScaleSpec.differentiableOn_remFactor`, `TwoScaleSpec.remFactor_eq_zero_iff`, `TwoScaleSpec.remFactor_eq_cexp_integral`, `TwoScaleSpec.hasProd_crContinuation`, `TwoScaleSpec.differentiableOn_crContinuation`, `TwoScaleSpec.crContinuation_eq_zero_iff`, `TwoScaleSpec.crContinuation_ne_zero_critical_line`, `TwoScaleSpec.zeroConfig`, `TwoScaleSpec.twoScaleZeroConfig_properties`, `exists_two_scale_integer_norm_euler_product`.
- Module `ExceptionalLayerTheory/NonrealZeroRepulsionAndCoMovingRemainders.lean` (namespace `GaloisForLFunctions.ExceptionalLayerTheory`):
  `zero_le_two_phase_cosine_scalar`, `zero_le_five_point_neg_re_logDeriv_riemannZeta`, `fiber_resolvent_le_re_logDeriv_xi`, `neg_re_logDeriv_riemannZeta_le_half_sub_fiber`, `two_zero_five_point_repulsion_inequality`, `pole_mainTerm_sub_simple_zero_pos`, `zeta_no_siegel_regime`, `tendsto_fixed_gap_mul_log_atTop`, `gaussianMBKernel_coMoving_eq`, `norm_gaussianMBKernel_coMoving`, `gaussianObservationRate_sub_coMovingRate`, `coMoving_supercritical_window_nonempty`, `tendsto_top_div_coMoving_zero_in_supercritical_window`, `tendsto_coMoving_div_top_zero_above_masking_threshold`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `ExceptionalLayerTheory` and `ArithmeticPositiveDuality`, `lake --old env lean` green

## Paper proof

### I. Exact orthogonal factorization of `AAL` and consequences for `ζ` (`[PROVED HERE]`)
Let `Z` be a `ZeroConfig` with global abscissa `Θ(Z) = zeroAbscissa Z` and asymptotic abscissa `Θ_∞(Z) = asymptoticAbscissa Z`. Define:
- `AsymptoticDeuringHeilbronn Z`: `¬AbscissaLaw Z → ApproachesLine Z`,
- `ExtremeDeuringHeilbronn Z`: `¬AbscissaLaw Z → (rightOf Z 0).Finite`.

1. **Equivalences of asymptotic and extreme repulsion.** By `abscissaLaw_iff_asymptoticAbscissa_eq_zeroAbscissa` and `approachesLine_iff_asymptoticAbscissa_eq_half`:
   - `AsymptoticDeuringHeilbronn Z ↔ AbscissaLaw Z ∨ ApproachesLine Z ↔ (Θ(Z) − Θ_∞(Z))(Θ_∞(Z) − 1/2) = 0`.
   - The following are equivalent (`TFAE`):
     (i) `ExtremeDeuringHeilbronn Z`;
     (ii) `AbscissaLaw Z ↔ AbscissaLawAt Z 0`;
     (iii) `AbscissaLawAt Z 0 → AbscissaLaw Z`;
     (iv) `AbscissaLaw Z ∨ (rightOf Z 0).Finite`.
     Indeed, `AbscissaLaw Z → AbscissaLawAt Z 0` always holds (`h = 0`). If (i) holds and `AbscissaLawAt Z 0` holds, suppose `¬AbscissaLaw Z`: then `(rightOf Z 0).Finite` by (i), so `AbscissaLawAt Z 0` gives `∀ ρ ∈ Z, Re ρ ≤ 1/2`, hence `Pure Z`, hence `AbscissaLaw Z`, contradiction. Conversely, if (iii) holds and `¬AbscissaLaw Z`, then `¬AbscissaLawAt Z 0`, whose negation supplies `(rightOf Z 0).Finite`.
   On `Z = zetaZeroConfig`, `(rightOf zetaZeroConfig 0).Finite ↔ FiniteOffLine` and `AbscissaLawAt zetaZeroConfig 0 ↔ (FiniteOffLine → RiemannHypothesis)` (`B13`). Hence `ZetaExtremeDeuringHeilbronn` is unconditionally equivalent to `AsymptoticAbscissaLaw ↔ (FiniteOffLine → RiemannHypothesis)`.

2. **Orthogonal factorization of `AbscissaLaw`.** Unconditionally for every `ZeroConfig`:
   `AbscissaLaw Z ↔ LinearAbscissaLaw Z ∧ AsymptoticDeuringHeilbronn Z ↔ LinearAbscissaLaw Z ∧ ExtremeDeuringHeilbronn Z ↔ AbscissaLawAt Z 0 ∧ ExtremeDeuringHeilbronn Z`.
   Specializing to `zetaZeroConfig`:
   - `AsymptoticAbscissaLaw ↔ ZetaLinearAbscissaLaw ∧ ZetaAsymptoticDeuringHeilbronn ↔ ZetaLinearAbscissaLaw ∧ ZetaExtremeDeuringHeilbronn ↔ (FiniteOffLine → RiemannHypothesis) ∧ ZetaExtremeDeuringHeilbronn`.
   - Under `ZetaExtremeDeuringHeilbronn`: `ZetaLinearAbscissaLaw ↔ (FiniteOffLine → RiemannHypothesis)` (collapsing the strict hierarchy `AAL ⊊ LinAt C₁ ⊊ LinAt C₂ ⊊ LinearAAL ⊊ B13`), `RiemannHypothesis ↔ ZerosApproachLine ∧ (FiniteOffLine → RiemannHypothesis)`, and together with `FiniteOffLine → RiemannHypothesis` all nine formulations (`RiemannHypothesis`, `ZerosApproachLine`, `FiniteOffLine`, `negIndex zetaKernel < ⊤`, bounded `nonrealZeroCount`, `xiCriticalSourceEnergy ≠ ⊤`, `EventualHadamardPositivity`, `EventualFilteredCentralGapBudget`, `FiniteDimensional ℝ oddBoundStateSpace`) become mutually equivalent.
   - Under `ZetaLinearAbscissaLawAt C` (`C ≥ 0`), any conditional asymptotic bound `¬AsymptoticAbscissaLaw → zetaAsymptoticAbscissa − 1/2 ≤ B` yields `¬AsymptoticAbscissaLaw → zetaZeroAbscissa − 1/2 ≤ C B`.
   - Under `¬AsymptoticAbscissaLaw`, for every `a > 0`, the symmetric shift `ξ(s + a)ξ(s − a)` violates `ExtremeDeuringHeilbronn`: its abscissas shift to `Θ + a > Θ_∞ + a`, while Hardy's critical-line zeros of `ξ` produce infinitely many off-line zeros on `Re s = 1/2 + a > 1/2`.

### II. Nonreal 5-point repulsion, absence of the Siegel regime, and co-moving remainder phase transition for `ζ` (`[PROVED HERE]`)
1. **Multiplicity-exact 5-point repulsion and absence of the Siegel regime.** For `1 < σ` and `γ₁, γ₂ ∈ ℝ`, expanding `−Re(ζ'/ζ(σ + it)) = ∑_{n≥1} Λ(n) n^{-σ} cos(t log n)` against `2(1 + cos u)(1 + cos v) = 2 + 2 cos u + 2 cos v + cos(v + u) + cos(v − u) ≥ 0` and retaining the full multiplicity fibres `m_j = card (xiZeroCopyFiber q_j.1)` via `re_logDeriv_xi_eq_realReciprocal_tsum` gives, for `1 < σ ≤ 2`, `4 ≤ γ₁`, and `γ₁ + 4 ≤ γ₂`:
   `2 m₁ / (σ − β₁) + 2 m₂ / (σ − β₂) ≤ 2 / (σ − 1) + log γ₁ + log γ₂ + (log(γ₂ + γ₁) + log(γ₂ − γ₁)) / 2 + 13 / 5`.
   For `m₁ = 1`, `2/(σ − 1) − 2/(σ − β₁) = 2(1 − β₁)/[(σ − 1)(σ − β₁)] > 0` for all `σ > 1`. Moreover, by `re_le_one_sub_of_zeta_zero` and `four_le_abs_im_of_zeta_zero`, every pair of nontrivial zeros `ρ₁, ρ₂` of `ζ` satisfies `1/58 < (1 − Re ρ₁) log(|Im ρ₁| · |Im ρ₂|)`; and for any fixed `β < 1`, `(1 − β) log t → +∞` as `t → +∞`. Thus `ζ(s)` possesses no Siegel Deuring–Heilbronn regime.

2. **Exact speed phase transition of the `exp(−at)` Gaussian prime current.** At `s = σ + it` and `y = e^{-at}` (`a > 0`), a fixed top-layer zero `ρ_top = β + iγ_top` has `gaussianObservationRate ρ_top σ a = a(β − σ)/2 − π/4`, whereas a co-moving remainder zero at `β_r + it` (`σ < β_r < β`) has zero vertical Gamma argument and exact positive mode `K(e^{-at}, β_r − σ) = (1/2) Γ((β_r − σ)/2) exp(a(β_r − σ)t / 2)`. Subtracting the rates cancels `σ`:
   `gaussianObservationRate ρ_top σ a − a(β_r − σ)/2 = a(β − β_r)/2 − π/4`.
   Hence on the nonempty window `π/(2(β − σ)) < a < π/(2(β − β_r))`, the top mode is supercritical yet `‖K_top / K_co‖ → 0`, whereas for `a > π/(2(β − β_r))`, `‖K_co / K_top‖ → 0`.

### III. Two-scale positive integer-norm Euler product with linear counting across `Re s = 1/2` (`[PROVED HERE]`)
Fix `1/2 < θ ≤ θ₂ < β < 2/3` and `γ > 0`, with base `DiscreteOneOff.Params` `P` (`μ = 1 − β`, `ν = (3μ − 1)/2`, `c₀ = (1 − e^{-μ})^3`).

1. **Continuous two-scale prime density.** Set `θ_0 := θ₂`, `θ_{n+1} := θ`, `U_0 := max 2 (32 / (c₀ (1 − θ₂)^2))`, `A_n := U_0 + n + 1`, `M_n := ⌈A_n (γ + 4 + n + 2^n e^{2 A_n}) / (2π)⌉₊ + 1`, and `ω_n := (π/2 + 2π M_n) / A_n`, so `ω_n > γ + 4 + n + 2^n e^{2 A_n}` and `cos(ω_n A_n) = 0`. Putting `g_n(t) := if A_n ≤ t then −2 e^{θ_n t} cos(ω_n t) / t else 0` and `w_∞ := ∑'_n g_n`, local finiteness makes `w_∞` continuous on `ℝ` with `|w_∞(t)| ≤ (1/4) P.w(t)` (`t > 0`), so `w := P.w + w_∞` satisfies `(3/4) P.w(t) ≤ w(t) ≤ (5/4) P.w(t)` and `w(u) − w(u/2)/4 > 0` for `u ≥ u₁ := 2 log(9/c₀) + 2`.

2. **Entire cutoff-Frullani factors and holomorphic patching of `G_∞`.** For `A > 0`, `F_A(z) := z exp(−∫_{(0,A]} (e^{-t} − e^{-zt})/t dt − ∫_{(A,∞)} e^{-t}/t dt)` is entire, vanishes iff `z = 0`, equals `exp(Φ_A(z))` on `ℂ \ (−∞, 0]` with `Φ_A(z) = −∫_{(A,∞)} e^{-zt}/t dt` on `{Re z > 0}`, and satisfies `‖Φ_A(z)‖ ≤ e^{-A Re z}/(A |Im z|)` for `Im z ≠ 0` by integrating `Φ_A'(z + x) = e^{-A(z+x)}/(z+x)` over `x ∈ (0, ∞)`. Patching finite products of `F_{A_n}(s − ρ_n) F_{A_n}(s − conj ρ_n)` (`ρ_n = θ_n + iω_n`) with convergent `exp(∑_{m≥K} (Φ_{A_m}(s − ρ_m) + Φ_{A_m}(s − conj ρ_m)))` defines `G_∞` holomorphic on `{Re s > 0}` whose zero set there is `{ρ_n, conj ρ_n : n ∈ ℕ}` and which equals `exp(∫_{(0,∞)} e^{-st} w_∞(t) dt)` on `{Re s > 1}`.

3. **Prime-square quantile discretization and integer-norm rounding.** Quantizing `V(x) := W(x) − W(x/2)/2 + W(min(x, u₁)/2)/2` via `V(t_k) = k + 1` and rounding `q_k := ⌈e^{t_k}⌉₊ ≥ 2` yields `∏_k (1 − q_k^{-s})^{-1} = ∑_n a_n n^{-s}` (`a_n ∈ ℕ`, `(1/N)∑_{n<N} a_n → A > 0`) continuing holomorphically to `{Re s > 1/3, s ≠ 1}` with zero set `{β ± iγ} ∪ {ρ_n, conj ρ_n : n ∈ ℕ}` and no zeros on `Re s = 1/2`. Symmetrizing `{1/2 < Re s < 1, F(s) = 0}` under `s ↦ 1 − conj s` produces a `ZeroConfig` realizing `(Θ, Θ₂, Θ_∞) = (β, θ₂, θ)`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Extreme Deuring–Heilbronn (`¬AAL ⇒ FiniteOffLine`), asymptotic Deuring–Heilbronn (`¬AAL ⇒ ZAL`), `AAL ⇔ B13`, and every sub-`Θ₂` graded repulsion bound `Θ_∞ − 1/2 ≤ f(β − Θ₂, γ)` (`f(β − Θ₂, γ) < θ₂ − 1/2`) are falsified across convergent integer-norm Euler products with nonnegative integer Dirichlet coefficients, linear summatory counting, and zero-free holomorphic continuation across `Re s = 1/2` (`exists_two_scale_integer_norm_euler_product`, `no_sub_ceiling_graded_deuring_heilbronn_on_integer_norm_euler_products`). High-ordinate cutoff-Frullani prime-density waves `−2 e^{θ_n t} cos(ω_n t)/t 1_{[A_n, ∞)}(t)` (`cos(ω_n A_n) = 0`, `ω_n ≫ 2^n e^{2 A_n}`) stay within `±(1/4) P.w(t)` globally while decaying off-cut as `O(2^{-n})`, planting infinitely many off-line zeros at arbitrary `(θ_n, ω_n)`. For `ζ(s)`, `1/58 < (1 − Re ρ₁) log(|Im ρ₁| · |Im ρ₂|)` (`zeta_no_siegel_regime`) excludes the Siegel regime, and in the `exp(−at)` Gaussian prime current a co-moving remainder zero at `β_r + it` dominates the supercritical top layer on `π/(2(β − σ)) < a < π/(2(β − β_r))` (`tendsto_top_div_coMoving_zero_in_supercritical_window`).
- **Strongest positive survivor:**
  1. Exact orthogonal factorization `AbscissaLaw ↔ LinearAbscissaLaw ∧ AsymptoticDeuringHeilbronn ↔ LinearAbscissaLaw ∧ ExtremeDeuringHeilbronn` (`abscissaLaw_orthogonal_factorization_tfae`, `asymptoticAbscissaLaw_orthogonal_factorization_tfae`) and strict 2×2 independence of `LinearAbscissaLaw` and `ExtremeDeuringHeilbronn` on positive integer-norm Euler products (`oneOff_euler_product_extremeDeuringHeilbronn_not_linear`, `twoScale_euler_product_linear_not_asymptoticDeuringHeilbronn`).
  2. Multiplicity-exact 5-point repulsion (`two_zero_five_point_repulsion_inequality`) and the `σ`-independent threshold `a_* = π/(2(β − β_r))` separating co-moving remainder dominance (`a < a_*`) from exponential top-layer masking (`a > a_*`) (`tendsto_coMoving_div_top_zero_above_masking_threshold`).
- **New insight:** Euler product positivity, natural prime norms, nonnegative integer Dirichlet coefficients, Wiener–Ikehara linear counting, and analytic continuation across `Re s = 1/2` permit both orthogonal failure modes of `AAL` independently (`Θ > Θ_∞ = 1/2` and `Θ > Θ_∞ = Θ₂ > 1/2`). Any Deuring–Heilbronn reduction `AAL ⇔ B13` for `ζ` must couple the Euler product to the functional equation `s ↔ 1 − s`.
- **Status:** Paper proof complete and unconditionally formalized in Lean 4 across `ExceptionalLayerTheory` and `ArithmeticPositiveDuality`.

## Log
- 2026-11-09 — created; proved; formalized.

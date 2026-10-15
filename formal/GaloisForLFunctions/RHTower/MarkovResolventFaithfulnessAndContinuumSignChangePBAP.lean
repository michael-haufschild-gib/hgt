import GaloisForLFunctions.RHTower.MarkovOriginBoundaryAbsorptionAndTrapezoidalPBAP

/-!
# Resolvent Faithfulness, Two-Sided Origin Control of `logValue`, and the Continuum Sign-Change Theorem on the Primitive Hyperplane and Odd Sector

This module establishes three foundational structural theorems on Route HF / PBAP:

1. **Section 1 (Two-Sided Origin Control of Autocorrelation Pairs, Pointwise Decay
   `|logValue f.1 n| ≤ (2 / √n) ∫ ‖f.1‖²`, and Upper Bound `bochnerResolventEnergy k_f ≤ 4 ∫ ‖f.1‖²`):**
   - Complementing the Spectral Dirichlet Difference Identity from Module 42, we prove the
     **Spectral Cosine Sum Identity** (`two_mul_integral_norm_sq_add_re_weilTest_pair_eq`):
     `2 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + (EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * (1 + Real.cos (r * u₀))) ≥ 0`.
   - Combining both identities gives the sharp two-sided Bochner bound
     (`abs_re_weilTest_add_neg_le_two_mul_integral_norm_sq`,
     `abs_atomPairRe_weilTest_le_two_mul_integral_norm_sq`):
     `|(EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re| ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`,
     and in particular `|atomPairRe (EF.weilTest f.1 f.1)| ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`.
   - Consequently (`abs_logValue_le_two_div_sqrt_mul_integral_norm_sq`,
     `abs_logValue_le_two_mul_integral_norm_sq`,
     `abs_weilContinuumLogProfile_le_two_div_sqrt_mul_integral_norm_sq`), every discrete node
     `logValue f.1 n` and continuum profile value `weilContinuumLogProfile f.1 x` is bounded in
     absolute value by `(2 / √x) * ∫ ‖f.1‖² ≤ 2 * ∫ ‖f.1‖²`.
   - Using `1 / (1 / 4 + r ^ 2) ≤ 4`, we prove the sharp upper bound
     (`bochnerResolventEnergy_weilTest_le_four_mul_integral_norm_sq`):
     `bochnerResolventEnergy (EF.weilTest f.1 f.1) ≤ 4 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`.

2. **Section 2 (Complete Vanishing of `bochnerResolventEnergy`, `atomPairRe`, `logValue`, and
   `primeBlindCounterterm` when `∫ ‖f.1‖² = 0`, and Strict Faithfulness
   `bochnerResolventEnergy k_f = 0 ↔ ∫ ‖f.1‖² = 0`):**
   - Since the resolvent multiplier `1 / (1 / 4 + r ^ 2)` is strictly positive for all `r ∈ ℝ`,
     `bochnerResolventEnergy (EF.weilTest f.1 f.1) = 0` forces `‖paperFT f.1 r‖ ^ 2 = 0` almost
     everywhere, which by Plancherel forces `∫ u : ℝ, ‖f.1 u‖ ^ 2 = 0`
     (`integral_norm_sq_eq_zero_of_bochnerResolventEnergy_eq_zero`,
     `bochnerResolventEnergy_weilTest_eq_zero_iff`).
   - Whenever `∫ u : ℝ, ‖f.1 u‖ ^ 2 = 0` (or equivalently `bochnerResolventEnergy k_f = 0`),
     `atomPairRe k_f = 0`, `logValue f.1 n = 0` for all `n : ℕ`, `logVector f = 0`,
     `primeBlindCounterterm lam f = 0` for every counterterm `lam : ℕ → ℝ`, and
     `0 ≤ markovCountertermEnergy lam f.1` (`markovCountertermEnergy_nonneg_of_bochnerResolventEnergy_eq_zero`).

3. **Section 3 (The Continuum Sign-Change / Overshoot Theorem on the Primitive Hyperplane and Odd
   Sector):**
   - On the primitive hyperplane `coshHalfMoment f = 0` (and in particular on all odd tests),
     `(∫ x, primeIntegrand k_F x ∂lebesguePart).re = -2 * sinhHalfMoment f ^ 2 - bochnerResolventEnergy k_F ≤ 0`.
   - Therefore, if `0 ≤ (∫ x, primeIntegrand k_F x ∂lebesguePart).re` (which holds whenever
     `0 ≤ primeBlindCounterterm unitStepCountertermWeight F + rightCellQuadratureDefect (ℓ_F) N`, or
     whenever `0 ≤ weilContinuumLogProfile F x` on `[1, N]`, or whenever `weilContinuumLogProfile F`
     is antitone on `[1, N]` with `k_F(±log N) = 0`), then `bochnerResolventEnergy k_F = 0`,
     `sinhHalfMoment f = 0`, `∫ ‖F‖² = 0`, `primeBlindCounterterm lam F = 0`, and
     **`0 ≤ markovCountertermEnergy lam F` (and `0 ≤ markovEnergy F`) holds unconditionally for
     every counterterm sequence `lam`**!
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: Two-Sided Origin Control of Autocorrelation Pairs, Pointwise Decay of `logValue`, and Upper Bound on `bochnerResolventEnergy` -/

/-- **Spectral Cosine Sum Identity**:
for every `f : WeilTestFn` and every shift `u₀ : ℝ`, the sum of the `n = 1` origin term
`2 * ∫ ‖f.1‖²` and the symmetric autocorrelation pair `(k_f(u₀) + k_f(-u₀)).re` equals the
nonnegative spectral integral
`(1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * (1 + Real.cos (r * u₀)))`. -/
theorem two_mul_integral_norm_sq_add_re_weilTest_pair_eq (f : WeilTestFn) (u₀ : ℝ) :
    2 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        (EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re =
      (1 / (2 * π)) *
        ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * (1 + Real.cos (r * u₀))) := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have hFk : Integrable (𝓕 (EF.weilTest f.1 f.1)) :=
    EF.integrable_fourier_of_contDiff_two hkd hkc
  have hP : Integrable fun r : ℝ => paperFT (EF.weilTest f.1 f.1) r :=
    EF.integrable_paperFT_ofReal hFk
  have hPn : ∀ r : ℝ, paperFT (EF.weilTest f.1 f.1) r = ((‖paperFT f.1 r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    rw [EF.paperFT_weilTest f.2.1.continuous f.2.1.continuous f.2.2 f.2.2, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 := by
    refine hP.norm.congr (Eventually.of_forall fun r => ?_)
    simp only
    rw [hPn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcos : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r * u₀)) := by
    refine (hsq.mul_const 2).mono' ?_ (Eventually.of_forall fun r => ?_)
    · exact (hsq.aestronglyMeasurable.mul (by fun_prop))
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hle : |Real.cos (r * u₀)| ≤ 1 := Real.abs_cos_le_one (r * u₀)
      nlinarith [sq_nonneg ‖paperFT f.1 r‖]
  rw [← LebesgueAtomWeil.integral_norm_sq_paperFT_eq f.2.1 f.2.2,
    re_weilTest_add_neg_eq_spectral_cos f u₀]
  have h2 : 2 * ((1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2) =
      (1 / (2 * π)) * ∫ r : ℝ, (‖paperFT f.1 r‖ ^ 2 * 2) := by
    rw [integral_mul_const]
    ring
  rw [h2, ← mul_add, ← integral_add (hsq.mul_const 2) hcos]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  ring

/-- **Lower Bound on Symmetric Autocorrelation Pairs by the Origin**:
for every `f : WeilTestFn` and every shift `u₀ : ℝ`,
`-(2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤ (EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re`. -/
theorem neg_two_mul_integral_norm_sq_le_re_weilTest_add_neg (f : WeilTestFn) (u₀ : ℝ) :
    -(2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      (EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re := by
  have hsum := two_mul_integral_norm_sq_add_re_weilTest_pair_eq f u₀
  have hnonneg : 0 ≤ (1 / (2 * π)) *
      ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * (1 + Real.cos (r * u₀))) := by
    refine mul_nonneg (by positivity) (integral_nonneg fun r => ?_)
    refine mul_nonneg (by positivity) ?_
    linarith [Real.neg_one_le_cos (r * u₀)]
  linarith

/-- **Two-Sided Absolute Value Bound on Symmetric Autocorrelation Pairs**:
for every `f : WeilTestFn` and every shift `u₀ : ℝ`,
`|(EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re| ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_re_weilTest_add_neg_le_two_mul_integral_norm_sq (f : WeilTestFn) (u₀ : ℝ) :
    |(EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re| ≤
      2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 :=
  abs_le.mpr ⟨neg_two_mul_integral_norm_sq_le_re_weilTest_add_neg f u₀,
    re_weilTest_add_neg_le_two_mul_integral_norm_sq f u₀⟩

/-- **Two-Sided Origin Bound on `atomPairRe`**:
for every `f : WeilTestFn`,
`|atomPairRe (EF.weilTest f.1 f.1)| ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_atomPairRe_weilTest_le_two_mul_integral_norm_sq (f : WeilTestFn) :
    |atomPairRe (EF.weilTest f.1 f.1)| ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 :=
  abs_re_weilTest_add_neg_le_two_mul_integral_norm_sq f (1 / 10000)

/-- **Pointwise `(2 / √n)` Decay Bound on `logValue f.1 n`**:
for every `f : WeilTestFn` and every `n : ℕ` with `1 ≤ n`,
`|logValue f.1 n| ≤ (2 / Real.sqrt n) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_logValue_le_two_div_sqrt_mul_integral_norm_sq (f : WeilTestFn) {n : ℕ} (hn : 1 ≤ n) :
    |logValue f.1 n| ≤ (2 / Real.sqrt n) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hre : logValue f.1 n =
      (EF.weilTest f.1 f.1 (Real.log n) + EF.weilTest f.1 f.1 (-Real.log n)).re /
        Real.sqrt n := rfl
  rw [hre, abs_div, abs_of_pos hsqrt_pos, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hsqrt_pos]
  exact abs_re_weilTest_add_neg_le_two_mul_integral_norm_sq f (Real.log n)

/-- **Uniform Origin Bound on `logValue f.1 n` for All `n : ℕ`**:
for every `f : WeilTestFn` and every `n : ℕ`,
`|logValue f.1 n| ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_logValue_le_two_mul_integral_norm_sq (f : WeilTestFn) (n : ℕ) :
    |logValue f.1 n| ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold logValue
    simp only [Nat.cast_zero, Real.sqrt_zero, div_zero, abs_zero]
    positivity
  · have h1 := abs_logValue_le_two_div_sqrt_mul_integral_norm_sq f hn
    have hsqrt1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    have hdiv : 2 / Real.sqrt n ≤ 2 := div_le_self (by norm_num) hsqrt1
    exact h1.trans (mul_le_mul_of_nonneg_right hdiv hnorm_nonneg)

/-- **Pointwise `(2 / √x)` Decay Bound on `weilContinuumLogProfile f.1 x`**:
for every `f : WeilTestFn` and every `x > 0`,
`|weilContinuumLogProfile f.1 x| ≤ (2 / Real.sqrt x) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_weilContinuumLogProfile_le_two_div_sqrt_mul_integral_norm_sq
    (f : WeilTestFn) {x : ℝ} (hx : 0 < x) :
    |weilContinuumLogProfile f.1 x| ≤ (2 / Real.sqrt x) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hre : weilContinuumLogProfile f.1 x =
      (EF.weilTest f.1 f.1 (Real.log x) + EF.weilTest f.1 f.1 (-Real.log x)).re /
        Real.sqrt x := by
    unfold weilContinuumLogProfile primeIntegrand
    rw [Complex.re_ofReal_mul, inv_mul_eq_div]
  rw [hre, abs_div, abs_of_pos hsqrt_pos, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hsqrt_pos]
  exact abs_re_weilTest_add_neg_le_two_mul_integral_norm_sq f (Real.log x)

/-- **Spectral Upper Bound `bochnerResolventEnergy k_f ≤ 4 ∫ ‖f.1‖²`**:
for every `f : WeilTestFn`, since `1 / (1 / 4 + r ^ 2) ≤ 4` for all `r ∈ ℝ`,
`bochnerResolventEnergy (EF.weilTest f.1 f.1) ≤ 4 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem bochnerResolventEnergy_weilTest_le_four_mul_integral_norm_sq (f : WeilTestFn) :
    bochnerResolventEnergy (EF.weilTest f.1 f.1) ≤ 4 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have hFk : Integrable (𝓕 (EF.weilTest f.1 f.1)) :=
    EF.integrable_fourier_of_contDiff_two hkd hkc
  have hP : Integrable fun r : ℝ => paperFT (EF.weilTest f.1 f.1) r :=
    EF.integrable_paperFT_ofReal hFk
  have hPn : ∀ r : ℝ, paperFT (EF.weilTest f.1 f.1) r = ((‖paperFT f.1 r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    rw [EF.paperFT_weilTest f.2.1.continuous f.2.1.continuous f.2.2 f.2.2, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 := by
    refine hP.norm.congr (Eventually.of_forall fun r => ?_)
    simp only
    rw [hPn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hres : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) := by
    refine (hsq.mul_const 4).mono' ?_ (Eventually.of_forall fun r => ?_)
    · exact hsq.aestronglyMeasurable.mul
        (continuous_const.div (by fun_prop) fun r => by positivity).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg r]
  rw [bochnerResolventEnergy_weilTest_eq f,
    ← LebesgueAtomWeil.integral_norm_sq_paperFT_eq f.2.1 f.2.2]
  have hmono : (∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2))) ≤
      ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * 4 := by
    refine integral_mono hres (hsq.mul_const 4) fun r => ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg r]
  rw [integral_mul_const] at hmono
  have hπ : 0 < 1 / (2 * π) := by positivity
  nlinarith

/-! ## Section 2: Complete Vanishing when `∫ ‖f.1‖² = 0` and Strict Faithfulness `bochnerResolventEnergy k_f = 0 ↔ ∫ ‖f.1‖² = 0` -/

/-- If `∫ u : ℝ, ‖f.1 u‖ ^ 2 = 0`, then `atomPairRe (EF.weilTest f.1 f.1) = 0`. -/
theorem atomPairRe_eq_zero_of_integral_norm_sq_eq_zero {f : WeilTestFn}
    (h0 : (∫ u : ℝ, ‖f.1 u‖ ^ 2) = 0) :
    atomPairRe (EF.weilTest f.1 f.1) = 0 := by
  have h := abs_atomPairRe_weilTest_le_two_mul_integral_norm_sq f
  rw [h0, mul_zero] at h
  exact abs_nonpos_iff.mp h

/-- If `∫ u : ℝ, ‖f.1 u‖ ^ 2 = 0`, then `logValue f.1 n = 0` for all `n : ℕ`. -/
theorem logValue_eq_zero_of_integral_norm_sq_eq_zero {f : WeilTestFn}
    (h0 : (∫ u : ℝ, ‖f.1 u‖ ^ 2) = 0) (n : ℕ) :
    logValue f.1 n = 0 := by
  have h := abs_logValue_le_two_mul_integral_norm_sq f n
  rw [h0, mul_zero] at h
  exact abs_nonpos_iff.mp h

/-- If `∫ u : ℝ, ‖f.1 u‖ ^ 2 = 0`, then `logVector f = 0`. -/
theorem logVector_eq_zero_of_integral_norm_sq_eq_zero {f : WeilTestFn}
    (h0 : (∫ u : ℝ, ‖f.1 u‖ ^ 2) = 0) :
    logVector f = 0 := by
  ext j
  rw [logVector_apply, Finsupp.coe_zero, Pi.zero_apply]
  exact logValue_eq_zero_of_integral_norm_sq_eq_zero h0 j.1

/-- If `∫ u : ℝ, ‖f.1 u‖ ^ 2 = 0`, then `primeBlindCounterterm lam f = 0` for every counterterm
sequence `lam : ℕ → ℝ`. -/
theorem primeBlindCounterterm_eq_zero_of_integral_norm_sq_eq_zero (lam : ℕ → ℝ) {f : WeilTestFn}
    (h0 : (∫ u : ℝ, ‖f.1 u‖ ^ 2) = 0) :
    primeBlindCounterterm lam f = 0 := by
  unfold primeBlindCounterterm
  rw [logVector_eq_zero_of_integral_norm_sq_eq_zero h0, map_zero]

/-- If `∫ u : ℝ, ‖f.1 u‖ ^ 2 = 0`, then `bochnerResolventEnergy (EF.weilTest f.1 f.1) = 0`. -/
theorem bochnerResolventEnergy_eq_zero_of_integral_norm_sq_eq_zero {f : WeilTestFn}
    (h0 : (∫ u : ℝ, ‖f.1 u‖ ^ 2) = 0) :
    bochnerResolventEnergy (EF.weilTest f.1 f.1) = 0 := by
  have hnonneg := bochnerResolventEnergy_weilTest_nonneg f
  have hle := bochnerResolventEnergy_weilTest_le_four_mul_integral_norm_sq f
  rw [h0, mul_zero] at hle
  linarith

/-- If `∫ u : ℝ, ‖f.1 u‖ ^ 2 = 0`, then `0 ≤ markovCountertermEnergy lam f.1` for every counterterm
sequence `lam : ℕ → ℝ`. -/
theorem markovCountertermEnergy_nonneg_of_integral_norm_sq_eq_zero (lam : ℕ → ℝ) {f : WeilTestFn}
    (h0 : (∫ u : ℝ, ‖f.1 u‖ ^ 2) = 0) :
    0 ≤ markovCountertermEnergy lam f.1 := by
  have h :=
    one_hundredth_l2_sub_atomPairRe_sub_bochnerResolventEnergy_sub_counterterm_le_markovCountertermEnergy
      lam f
  rw [h0, atomPairRe_eq_zero_of_integral_norm_sq_eq_zero h0,
    bochnerResolventEnergy_eq_zero_of_integral_norm_sq_eq_zero h0,
    primeBlindCounterterm_eq_zero_of_integral_norm_sq_eq_zero lam h0] at h
  linarith

/-- **Strict Faithfulness of `bochnerResolventEnergy`**:
for every `f : WeilTestFn`, if `bochnerResolventEnergy (EF.weilTest f.1 f.1) = 0`, then
`∫ u : ℝ, ‖f.1 u‖ ^ 2 = 0`. -/
theorem integral_norm_sq_eq_zero_of_bochnerResolventEnergy_eq_zero {f : WeilTestFn}
    (h0 : bochnerResolventEnergy (EF.weilTest f.1 f.1) = 0) :
    (∫ u : ℝ, ‖f.1 u‖ ^ 2) = 0 := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have hFk : Integrable (𝓕 (EF.weilTest f.1 f.1)) :=
    EF.integrable_fourier_of_contDiff_two hkd hkc
  have hP : Integrable fun r : ℝ => paperFT (EF.weilTest f.1 f.1) r :=
    EF.integrable_paperFT_ofReal hFk
  have hPn : ∀ r : ℝ, paperFT (EF.weilTest f.1 f.1) r = ((‖paperFT f.1 r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    rw [EF.paperFT_weilTest f.2.1.continuous f.2.1.continuous f.2.2 f.2.2, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 := by
    refine hP.norm.congr (Eventually.of_forall fun r => ?_)
    simp only
    rw [hPn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hres : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) := by
    refine (hsq.mul_const 4).mono' ?_ (Eventually.of_forall fun r => ?_)
    · exact hsq.aestronglyMeasurable.mul
        (continuous_const.div (by fun_prop) fun r => by positivity).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg r]
  have hint0 : (∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2))) = 0 := by
    have h1 := bochnerResolventEnergy_weilTest_eq f
    rw [h0] at h1
    have hπ : (1 / (2 * π) : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1.symm).resolve_left hπ
  have hae : (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2))) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun r => by positivity) hres).mp hint0
  have hae_sq : (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2) =ᵐ[volume] (0 : ℝ → ℝ) := by
    filter_upwards [hae] with r hr
    simp only [Pi.zero_apply] at hr ⊢
    have hpos : (1 / (1 / 4 + r ^ 2) : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hr).resolve_right hpos
  rw [← LebesgueAtomWeil.integral_norm_sq_paperFT_eq f.2.1 f.2.2,
    integral_congr_ae hae_sq, Pi.zero_def, integral_zero, mul_zero]

/-- **Exact Equivalence `bochnerResolventEnergy k_f = 0 ↔ ∫ ‖f.1‖² = 0`**:
for every `f : WeilTestFn`, the Bochner–Poisson resolvent energy vanishes if and only if the `L²`
norm squared of `f.1` vanishes. -/
theorem bochnerResolventEnergy_weilTest_eq_zero_iff (f : WeilTestFn) :
    bochnerResolventEnergy (EF.weilTest f.1 f.1) = 0 ↔ (∫ u : ℝ, ‖f.1 u‖ ^ 2) = 0 :=
  ⟨integral_norm_sq_eq_zero_of_bochnerResolventEnergy_eq_zero,
    bochnerResolventEnergy_eq_zero_of_integral_norm_sq_eq_zero⟩

/-- If `bochnerResolventEnergy (EF.weilTest f.1 f.1) = 0`, then `0 ≤ markovCountertermEnergy lam f.1`
for every counterterm sequence `lam : ℕ → ℝ`. -/
theorem markovCountertermEnergy_nonneg_of_bochnerResolventEnergy_eq_zero
    (lam : ℕ → ℝ) {f : WeilTestFn} (h0 : bochnerResolventEnergy (EF.weilTest f.1 f.1) = 0) :
    0 ≤ markovCountertermEnergy lam f.1 :=
  markovCountertermEnergy_nonneg_of_integral_norm_sq_eq_zero lam
    (integral_norm_sq_eq_zero_of_bochnerResolventEnergy_eq_zero h0)

/-! ## Section 3: The Continuum Sign-Change / Overshoot Theorem on the Primitive Hyperplane and Odd Sector -/

/-- **Continuum Vanishing Law on the Primitive Hyperplane**:
for every real test `f ∈ C²_c(ℝ)` on the primitive hyperplane `coshHalfMoment f = 0`, if
`0 ≤ (∫ x, primeIntegrand k_F x ∂lebesguePart).re`, then `bochnerResolventEnergy k_F = 0`,
`sinhHalfMoment f = 0`, and `∫ u : ℝ, ‖F u‖ ^ 2 = 0`. -/
theorem bochnerResolventEnergy_and_l2_eq_zero_of_lebesguePart_nonneg_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hleb : 0 ≤ (∫ x, primeIntegrand
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) x ∂lebesguePart).re) :
    bochnerResolventEnergy
        (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) = 0 ∧
      sinhHalfMoment f = 0 ∧
      (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) = 0 := by
  have heq : (∫ x, primeIntegrand
        (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) x
        ∂lebesguePart).re =
      2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 -
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    re_integral_primeIntegrand_lebesguePart_ofReal_eq hf hfc
  rw [hcosh] at heq
  have hres_nonneg := bochnerResolventEnergy_weilTest_nonneg (realWeilTestFn f hf hfc)
  have hsinh_nonneg : 0 ≤ sinhHalfMoment f ^ 2 := sq_nonneg _
  have hres0 : bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) = 0 := by
    linarith
  have hsinh_sq0 : sinhHalfMoment f ^ 2 = 0 := by
    linarith
  exact ⟨hres0, sq_eq_zero_iff.mp hsinh_sq0,
    integral_norm_sq_eq_zero_of_bochnerResolventEnergy_eq_zero hres0⟩

/-- **Unconditional Markov Positivity under Nonnegative Continuum `lebesguePart` Integral on the
Primitive Hyperplane**:
for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` and every counterterm sequence
`lam : ℕ → ℝ`, if `0 ≤ (∫ x, primeIntegrand k_F x ∂lebesguePart).re`, then
`0 ≤ markovCountertermEnergy lam F` (and in particular `0 ≤ markovEnergy F`). -/
theorem markovCountertermEnergy_nonneg_of_lebesguePart_nonneg_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hleb : 0 ≤ (∫ x, primeIntegrand
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) x ∂lebesguePart).re) :
    0 ≤ markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 :=
  markovCountertermEnergy_nonneg_of_bochnerResolventEnergy_eq_zero lam
    (bochnerResolventEnergy_and_l2_eq_zero_of_lebesguePart_nonneg_of_cosh_zero
      hf hfc hcosh hleb).1

/-- **Unconditional Markov Positivity under Nonnegative Continuum Profile `ℓ_F ≥ 0` on `[1, N]`**:
for every real test `f ∈ C²_c(ℝ)` on the primitive hyperplane `coshHalfMoment f = 0`, if `1 ≤ N` is
a support cutoff of `k_F` and `0 ≤ weilContinuumLogProfile F x` for all `x ∈ [1, N]`, then
`∫ ‖F‖² = 0` and `0 ≤ markovCountertermEnergy lam F` for every counterterm `lam : ℕ → ℝ`. -/
theorem markovCountertermEnergy_nonneg_of_weilContinuumLogProfile_nonneg_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hnonneg : ∀ x ∈ Icc (1 : ℝ) (N : ℝ),
      0 ≤ weilContinuumLogProfile (realWeilTestFn f hf hfc).1 x) :
    0 ≤ markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have hleb : 0 ≤ (∫ x, primeIntegrand
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) x ∂lebesguePart).re := by
    rw [re_integral_primeIntegrand_lebesguePart_eq_intervalIntegral
      (realWeilTestFn f hf hfc) (by exact_mod_cast hN1) hN]
    exact intervalIntegral.integral_nonneg (by exact_mod_cast hN1) hnonneg
  exact markovCountertermEnergy_nonneg_of_lebesguePart_nonneg_of_cosh_zero lam hf hfc hcosh hleb

/-- **Unconditional Markov Positivity under Antitone (Nonincreasing) Continuum Profile on `[1, N]`**:
if `f ∈ C²_c(ℝ)` lies on the primitive hyperplane `coshHalfMoment f = 0` (e.g. `f` is odd) and
`weilContinuumLogProfile F` is antitone on `[1, N]` with `k_F(±log x) = 0` for `x ≥ N`, then
`0 ≤ weilContinuumLogProfile F x` on `[1, N]`, so `∫ ‖F‖² = 0` and `0 ≤ markovCountertermEnergy lam F`
for every counterterm `lam : ℕ → ℝ`. -/
theorem markovCountertermEnergy_nonneg_of_antitoneOn_weilContinuumLogProfile_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hanti : AntitoneOn (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) (Icc (1 : ℝ) (N : ℝ))) :
    0 ≤ markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have hZeroN : weilContinuumLogProfile (realWeilTestFn f hf hfc).1 (N : ℝ) = 0 := by
    rw [weilContinuumLogProfile_natCast_eq_logValue]
    simp [logValue, hN0.1, hN0.2]
  have hnonneg : ∀ x ∈ Icc (1 : ℝ) (N : ℝ),
      0 ≤ weilContinuumLogProfile (realWeilTestFn f hf hfc).1 x := by
    intro x hx
    rw [← hZeroN]
    exact hanti hx ⟨by exact_mod_cast hN1, le_rfl⟩ hx.2
  exact markovCountertermEnergy_nonneg_of_weilContinuumLogProfile_nonneg_of_cosh_zero
    lam hf hfc hcosh hN1 hN hnonneg

end RHTower

end

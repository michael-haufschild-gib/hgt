import GaloisForLFunctions.RHTower.PrimeArchMomentMeasureRH
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Compact Markov germs feed the all-degree RH capstone

This module closes the downstream interface between a source-produced compact Markov transform and
the existing positive moment representation criterion for RH.  If the ordinary completed-seam
moment germ agrees near zero with the Markov transform of one finite positive measure carried by a
compact nonnegative interval, differentiation under the integral identifies every source moment
with the corresponding measure moment.  The all-degree Hankel capstone then proves RH.

The remaining producer problem is explicit: construct the measure and prove the local germ
identity.  No positivity conclusion or RH premise is included in that producer interface.
-/

open Complex Filter Function Metric Set Topology MeasureTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- The `k`-th differentiated kernel moment of a compact Markov transform. -/
def compactMarkovKernelMoment (μ : Measure ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) ^ k * (1 - (x : ℂ) * z)⁻¹ ^ (k + 1) ∂μ

/-- Markov transform normalized at the origin: `K_μ(z) = ∫ (1 - xz)⁻¹ dμ(x)`. -/
def compactMarkovTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  compactMarkovKernelMoment μ 0 z

theorem compactMarkovKernelMoment_zero (μ : Measure ℝ) (z : ℂ) :
    compactMarkovKernelMoment μ 0 z = compactMarkovTransform μ z := rfl

theorem norm_one_sub_real_mul_ge_half
    {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) :
    (1 : ℝ) / 2 ≤ ‖1 - (x : ℂ) * z‖ := by
  have hxnorm : ‖(x : ℂ)‖ ≤ B := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have hprod : ‖(x : ℂ) * z‖ < (1 : ℝ) / 2 := by
    rw [norm_mul]
    calc
      ‖(x : ℂ)‖ * ‖z‖ ≤ B * ‖z‖ := by gcongr
      _ < B * (1 / (2 * B)) := mul_lt_mul_of_pos_left hz hB
      _ = (1 : ℝ) / 2 := by field_simp
  have htri : (1 : ℝ) ≤ ‖1 - (x : ℂ) * z‖ + ‖(x : ℂ) * z‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖(1 - (x : ℂ) * z) + (x : ℂ) * z‖ := by ring_nf
      _ ≤ ‖1 - (x : ℂ) * z‖ + ‖(x : ℂ) * z‖ := norm_add_le _ _
  linarith

theorem norm_inv_one_sub_real_mul_le_two
    {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) :
    ‖(1 - (x : ℂ) * z)⁻¹‖ ≤ 2 := by
  rw [norm_inv]
  calc
    ‖1 - (x : ℂ) * z‖⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ :=
      inv_anti₀ (by norm_num) (norm_one_sub_real_mul_ge_half hB hx hz)
    _ = 2 := by norm_num

/-- Compact support makes every Markov kernel moment integrable inside a common disk. -/
theorem integrable_compactMarkovKernel
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B : ℝ} (hB : 0 < B) (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) (k : ℕ) :
    Integrable (fun x : ℝ =>
      (x : ℂ) ^ k * (1 - (x : ℂ) * z)⁻¹ ^ (k + 1)) μ := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ =>
      (x : ℂ) ^ k * (1 - (x : ℂ) * z)⁻¹ ^ (k + 1)) μ := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  refine Integrable.of_bound hmeas (B ^ k * 2 ^ (k + 1)) ?_
  filter_upwards [hbound] with x hx
  rw [norm_mul, norm_pow, norm_pow]
  have hxnorm : ‖(x : ℂ)‖ ≤ B := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have hinv := norm_inv_one_sub_real_mul_le_two hB hx hz
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxnorm k)
    (pow_le_pow_left₀ (norm_nonneg _) hinv (k + 1)) (by positivity) (by positivity)

theorem norm_lt_markov_radius_of_mem_ball
    {B : ℝ} {z₀ z : ℂ}
    (hz : z ∈ Metric.ball z₀ (1 / (2 * B) - ‖z₀‖)) :
    ‖z‖ < 1 / (2 * B) := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  calc
    ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
    _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
    _ < 1 / (2 * B) := by linarith

private theorem norm_compactMarkovKernelDerivative_le
    {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B)
    (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) :
    ‖((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ (k + 1) *
        (1 - (x : ℂ) * z)⁻¹ ^ (k + 2)‖ ≤
      ((k + 1 : ℕ) : ℝ) * B ^ (k + 1) * 2 ^ (k + 2) := by
  have hxnorm : ‖(x : ℂ)‖ ≤ B := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have hinv := norm_inv_one_sub_real_mul_le_two hB hx hz
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hxnorm (k + 1)) (by positivity))
    (pow_le_pow_left₀ (norm_nonneg _) hinv (k + 2)) (by positivity) (by positivity)

private theorem hasDerivAt_compactMarkovKernelIntegrand
    {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B)
    (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) :
    HasDerivAt (fun w : ℂ =>
        (x : ℂ) ^ k * (1 - (x : ℂ) * w)⁻¹ ^ (k + 1))
      (((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ (k + 1) *
        (1 - (x : ℂ) * z)⁻¹ ^ (k + 2)) z := by
  have hdennorm := norm_one_sub_real_mul_ge_half hB hx hz
  have hden : 1 - (x : ℂ) * z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hdennorm
    norm_num at hdennorm
  have hbase : HasDerivAt (fun w : ℂ => 1 - (x : ℂ) * w) (-(x : ℂ)) z := by
    simpa using (hasDerivAt_const z (1 : ℂ)).sub
      ((hasDerivAt_id z).const_mul (x : ℂ))
  have hinv : HasDerivAt (fun w : ℂ => (1 - (x : ℂ) * w)⁻¹)
      ((x : ℂ) * (1 - (x : ℂ) * z)⁻¹ ^ 2) z := by
    have h := hbase.inv hden
    convert h using 1
    field_simp
  have hpow := hinv.pow (k + 1)
  have h := hpow.const_mul ((x : ℂ) ^ k)
  convert h using 1
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [pow_add]
  ring

/-- Differentiating the `k`-th compact Markov kernel moment raises its order. -/
theorem hasDerivAt_compactMarkovKernelMoment
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B : ℝ} (hB : 0 < B) (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B)
    (k : ℕ) {z₀ : ℂ} (hz₀ : ‖z₀‖ < 1 / (2 * B)) :
    HasDerivAt (compactMarkovKernelMoment μ k)
      (((k + 1 : ℕ) : ℂ) * compactMarkovKernelMoment μ (k + 1) z₀) z₀ := by
  set s : Set ℂ := Metric.ball z₀ (1 / (2 * B) - ‖z₀‖) with hs
  have hrpos : 0 < 1 / (2 * B) - ‖z₀‖ := sub_pos.mpr hz₀
  have hsnhds : s ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hmem : ∀ z ∈ s, ‖z‖ < 1 / (2 * B) := by
    intro z hz
    exact norm_lt_markov_radius_of_mem_ball (by simpa [hs] using hz)
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable
      (fun x : ℝ => (x : ℂ) ^ k * (1 - (x : ℂ) * z)⁻¹ ^ (k + 1)) μ := by
    intro z
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hmeas' : AEStronglyMeasurable (fun x : ℝ =>
      ((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ (k + 1) *
        (1 - (x : ℂ) * z₀)⁻¹ ^ (k + 2)) μ := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hmajor : ∀ᵐ x : ℝ ∂μ, ∀ z ∈ s,
      ‖((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ (k + 1) *
          (1 - (x : ℂ) * z)⁻¹ ^ (k + 2)‖ ≤
        ((k + 1 : ℕ) : ℝ) * B ^ (k + 1) * 2 ^ (k + 2) := by
    filter_upwards [hbound] with x hx z hz
    exact norm_compactMarkovKernelDerivative_le hB hx k (hmem z hz)
  have hdiff : ∀ᵐ x : ℝ ∂μ, ∀ z ∈ s,
      HasDerivAt (fun w : ℂ =>
          (x : ℂ) ^ k * (1 - (x : ℂ) * w)⁻¹ ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ (k + 1) *
          (1 - (x : ℂ) * z)⁻¹ ^ (k + 2)) z := by
    filter_upwards [hbound] with x hx z hz
    exact hasDerivAt_compactMarkovKernelIntegrand hB hx k (hmem z hz)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun (z : ℂ) (x : ℝ) =>
      (x : ℂ) ^ k * (1 - (x : ℂ) * z)⁻¹ ^ (k + 1))
    (F' := fun (z : ℂ) (x : ℝ) =>
      ((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ (k + 1) *
        (1 - (x : ℂ) * z)⁻¹ ^ (k + 2))
    (bound := fun _ : ℝ =>
      ((k + 1 : ℕ) : ℝ) * B ^ (k + 1) * 2 ^ (k + 2))
    hsnhds (Filter.Eventually.of_forall fun z => hmeas z)
    (integrable_compactMarkovKernel μ hB hbound hz₀ k) hmeas' hmajor
    (integrable_const _) hdiff
  have hval :
      (∫ x : ℝ, ((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ (k + 1) *
          (1 - (x : ℂ) * z₀)⁻¹ ^ (k + 2) ∂μ) =
        ((k + 1 : ℕ) : ℂ) * compactMarkovKernelMoment μ (k + 1) z₀ := by
    simp only [mul_assoc, integral_const_mul]
    rfl
  rw [← hval]
  exact hmain.2

/-- Every iterated derivative of a compact Markov transform is its kernel moment times `k!`. -/
theorem iteratedDeriv_compactMarkovTransform
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B : ℝ} (hB : 0 < B) (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B) :
    ∀ (k : ℕ) {z : ℂ}, ‖z‖ < 1 / (2 * B) →
      iteratedDeriv k (compactMarkovTransform μ) z =
        ((Nat.factorial k : ℕ) : ℂ) * compactMarkovKernelMoment μ k z := by
  intro k
  induction k with
  | zero =>
      intro z hz
      rw [iteratedDeriv_zero, compactMarkovKernelMoment_zero]
      simp
  | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have hopen : IsOpen {w : ℂ | ‖w‖ < 1 / (2 * B)} :=
        isOpen_lt continuous_norm continuous_const
      have hev : iteratedDeriv k (compactMarkovTransform μ) =ᶠ[nhds z]
          fun w => ((Nat.factorial k : ℕ) : ℂ) * compactMarkovKernelMoment μ k w := by
        filter_upwards [hopen.mem_nhds hz] with w hw
        exact ih hw
      rw [hev.deriv_eq,
        deriv_const_mul _
          (hasDerivAt_compactMarkovKernelMoment μ hB hbound k hz).differentiableAt,
        (hasDerivAt_compactMarkovKernelMoment μ hB hbound k hz).deriv,
        Nat.factorial_succ]
      push_cast
      ring

theorem compactMarkovKernelMoment_zero_node
    (μ : Measure ℝ) (k : ℕ) :
    compactMarkovKernelMoment μ k 0 = ∫ x : ℝ, (x : ℂ) ^ k ∂μ := by
  simp [compactMarkovKernelMoment]

/-- A finite compactly supported measure has an analytic Markov transform at the origin. -/
theorem analyticAt_compactMarkovTransform
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B : ℝ} (hB : 0 < B) (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B) :
    AnalyticAt ℂ (compactMarkovTransform μ) 0 := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hdisk : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 / (2 * B) :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds
      (by simpa using (show (0 : ℝ) < 1 / (2 * B) by positivity))
  filter_upwards [hdisk] with z hz
  simpa only [compactMarkovTransform] using
    (hasDerivAt_compactMarkovKernelMoment μ hB hbound 0 hz).differentiableAt

/-- Ordinary (non-interleaved) generating series of the completed source moments. -/
def completedSeamMomentPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => (normalizedPrimeArchMoment n : ℂ))

/-- Analytic ordinary moment germ of the completed prime--archimedean source. -/
def completedSeamMomentGerm : ℂ → ℂ :=
  completedSeamMomentPowerSeries.sum

private theorem normalizedPrimeArchMoment_cast_eq_xiCentralReciprocalMoment (n : ℕ) :
    (normalizedPrimeArchMoment n : ℂ) = xiCentralReciprocalMoment n := by
  simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
    primeArchSourceMoment_eq_xiCentralReciprocalMoment n

/-- The ordinary source germ is its coefficientwise power series. -/
theorem completedSeamMomentGerm_eq_tsum (z : ℂ) :
    completedSeamMomentGerm z =
      ∑' n : ℕ, (normalizedPrimeArchMoment n : ℂ) * z ^ n := by
  rw [completedSeamMomentGerm, completedSeamMomentPowerSeries]
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (normalizedPrimeArchMoment n : ℂ)) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

/-- Squaring the centered coordinate recovers the existing even Xi central-moment germ. -/
theorem completedSeamMomentGerm_sq_eq_xiCentralMomentGerm (z : ℂ) :
    completedSeamMomentGerm (z ^ 2) = xiCentralMomentGerm z := by
  rw [completedSeamMomentGerm_eq_tsum, xiCentralMomentGerm_eq_tsum_even]
  apply tsum_congr
  intro n
  rw [normalizedPrimeArchMoment_cast_eq_xiCentralReciprocalMoment, pow_mul]

/-- The new ordinary seam germ is source-facing: after the seam-square substitution it agrees
locally with the pre-existing normalized continued prime--Gamma germ. -/
theorem completedSeamMomentGerm_sq_eventuallyEq_normalizedPrimeArchMomentGerm :
    (fun z : ℂ => completedSeamMomentGerm (z ^ 2)) =ᶠ[𝓝 0]
      normalizedPrimeArchMomentGerm := by
  calc
    (fun z : ℂ => completedSeamMomentGerm (z ^ 2)) =ᶠ[𝓝 0]
        xiCentralMomentGerm :=
      Filter.Eventually.of_forall completedSeamMomentGerm_sq_eq_xiCentralMomentGerm
    _ =ᶠ[𝓝 0] normalizedPrimeArchMomentGerm := by
      simpa only [normalizedPrimeArchMomentGerm] using
        normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm.symm

/-- The ordinary source moment series has positive radius of convergence. -/
theorem completedSeamMomentPowerSeries_radius_pos :
    0 < completedSeamMomentPowerSeries.radius := by
  obtain ⟨M, hM, hbound⟩ := exists_xiZeroCopyReciprocalSquare_norm_bound
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let r : ℝ≥0 := ⟨1 / (2 * M), by positivity⟩
  let S : ℝ := ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖
  have hrad : (r : ℝ≥0∞) ≤ completedSeamMomentPowerSeries.radius := by
    apply FormalMultilinearSeries.le_radius_of_bound
      (p := completedSeamMomentPowerSeries) S
    intro k
    rw [completedSeamMomentPowerSeries, FormalMultilinearSeries.ofScalars_norm]
    have hmoment := norm_xiCentralReciprocalMoment_le hbound k
    have hcoef : ‖(normalizedPrimeArchMoment k : ℂ)‖ ≤ M ^ k * S := by
      rw [normalizedPrimeArchMoment_cast_eq_xiCentralReciprocalMoment]
      exact hmoment
    change ‖(normalizedPrimeArchMoment k : ℂ)‖ * (1 / (2 * M)) ^ k ≤ S
    calc
      ‖(normalizedPrimeArchMoment k : ℂ)‖ * (1 / (2 * M)) ^ k ≤
          (M ^ k * S) * (1 / (2 * M)) ^ k :=
        mul_le_mul_of_nonneg_right hcoef (pow_nonneg (by positivity) _)
      _ = S * (M * (1 / (2 * M))) ^ k := by
        rw [mul_pow]
        ring
      _ = S * (1 / 2) ^ k := by
        rw [show M * (1 / (2 * M)) = (1 / 2 : ℝ) by field_simp]
      _ ≤ S := by
        exact mul_le_of_le_one_right (tsum_nonneg fun _ => norm_nonneg _)
          (pow_le_one₀ (by norm_num) (by norm_num))
  have hrpos : 0 < r := by
    apply NNReal.coe_pos.mp
    change 0 < 1 / (2 * M)
    positivity
  exact (ENNReal.coe_pos.mpr hrpos).trans_le hrad

theorem analyticAt_completedSeamMomentGerm :
    AnalyticAt ℂ completedSeamMomentGerm 0 := by
  exact ⟨completedSeamMomentPowerSeries,
    completedSeamMomentPowerSeries.hasFPowerSeriesOnBall
      completedSeamMomentPowerSeries_radius_pos |>.hasFPowerSeriesAt⟩

/-- Taylor extraction from the ordinary source moment germ. -/
theorem iteratedDeriv_completedSeamMomentGerm (n : ℕ) :
    iteratedDeriv n completedSeamMomentGerm 0 =
      ((Nat.factorial n : ℕ) : ℂ) * normalizedPrimeArchMoment n := by
  have hp := completedSeamMomentPowerSeries.hasFPowerSeriesOnBall
    completedSeamMomentPowerSeries_radius_pos
  have hfac := hp.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  rw [completedSeamMomentPowerSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    one_pow, smul_eq_mul, mul_one] at hfac
  rw [completedSeamMomentGerm]
  simpa only [nsmul_eq_mul] using hfac.symm

/-- One compact positive Markov transform agrees locally with the completed source moment germ. -/
def PrimeArchCompactMarkovGermRepresentation : Prop :=
  ∃ (μ : Measure ℝ) (B : ℝ),
    IsFiniteMeasure μ ∧
    0 < B ∧
    (∀ᵐ x : ℝ ∂μ, 0 ≤ x ∧ |x| ≤ B) ∧
    completedSeamMomentGerm =ᶠ[𝓝 0] compactMarkovTransform μ

/-- Any ordinary-variable Markov realization also realizes the actual normalized completed source
after the seam-square substitution. -/
theorem normalizedPrimeArchMomentGerm_eventuallyEq_compactMarkovTransform_sq
    {μ : Measure ℝ}
    (hgerm : completedSeamMomentGerm =ᶠ[𝓝 0] compactMarkovTransform μ) :
    normalizedPrimeArchMomentGerm =ᶠ[𝓝 0]
      fun z : ℂ => compactMarkovTransform μ (z ^ 2) := by
  have hsquare : Tendsto (fun z : ℂ => z ^ 2) (𝓝 0) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => z ^ 2) (𝓝 0) (𝓝 ((0 : ℂ) ^ 2)) :=
      (continuous_id.pow 2).continuousAt
    norm_num at h
    exact h
  exact completedSeamMomentGerm_sq_eventuallyEq_normalizedPrimeArchMomentGerm.symm.trans
    (hgerm.comp_tendsto hsquare)

/-- A compact Markov germ representation supplies the exact all-degree positive moment measure. -/
theorem primeArchMomentRepresentation_of_compactMarkovGerm
    (hrep : PrimeArchCompactMarkovGermRepresentation) :
    PrimeArchMomentRepresentation := by
  obtain ⟨μ, B, hfinite, hB, hsupport, hgerm⟩ := hrep
  letI : IsFiniteMeasure μ := hfinite
  have hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B := hsupport.mono fun _ hx => hx.2
  refine ⟨μ, ?_, ?_⟩
  · intro n
    have hder := hgerm.iteratedDeriv_eq n
    rw [iteratedDeriv_completedSeamMomentGerm,
      iteratedDeriv_compactMarkovTransform μ hB hbound n
        (by simpa using (show (0 : ℝ) < 1 / (2 * B) by positivity)),
      compactMarkovKernelMoment_zero_node] at hder
    have hintc : (∫ x : ℝ, (x : ℂ) ^ n ∂μ) =
        ((∫ x : ℝ, x ^ n ∂μ : ℝ) : ℂ) := by
      simpa using (integral_ofReal (X := ℝ) (μ := μ) (𝕜 := ℂ)
        (f := fun x : ℝ => x ^ n))
    rw [hintc] at hder
    have hfacne : (((Nat.factorial n : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    exact Complex.ofReal_inj.mp (mul_left_cancel₀ hfacne hder)
  · intro n
    have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ n) μ := by
      exact (continuous_id.pow n).aestronglyMeasurable
    refine Integrable.of_bound hmeas (B ^ n) ?_
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) hx n

/-- **Right-to-left RH capstone.** Local compact Markov realization of the source germ proves RH. -/
theorem riemannHypothesis_of_primeArchCompactMarkovGermRepresentation
    (hrep : PrimeArchCompactMarkovGermRepresentation) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchMomentRepresentation
    (primeArchMomentRepresentation_of_compactMarkovGerm hrep)

end

end RHTower

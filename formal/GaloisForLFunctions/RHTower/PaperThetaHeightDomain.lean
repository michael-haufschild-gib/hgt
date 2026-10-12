import GaloisForLFunctions.RHTower.PaperThetaBoundedDomain

/-! # Exact and limiting height recovery of the actual theta modes

The paper's literal height cutoffs become stationary on the divisor domain.
High-tilt modes have strictly positive error at every finite cutoff, with
geometric L¹ convergence paid by their proven logarithmic admission.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry FourierLLogL

private theorem height_threshold_tendsto :
    Tendsto (fun N : ℕ => Real.exp ((2 : ℝ) ^ (N + 1))) atTop atTop := by
  apply Real.tendsto_exp_atTop.comp
  simpa only [pow_succ] using
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
      (by norm_num : (0 : ℝ) < 2)

/-- Divisor-or-zero modes are fixed pointwise by every sufficiently high cutoff. -/
theorem eventually_heightCutoff_divisor (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    ∀ᶠ N : ℕ in atTop, paperFourierHeightCutoff (circleMode z.val) N = circleMode z.val := by
  obtain ⟨C, hC⟩ := exists_bound_circleMode z
  filter_upwards [height_threshold_tendsto.eventually (eventually_gt_atTop C)] with N hN
  funext x
  simp [paperFourierHeightCutoff, (hC x).trans_lt hN]

/-- A finite exact a.e. cutoff exists precisely on the bounded theta domain. -/
theorem exists_exact_heightCutoff_iff (z : ℂ) :
    (∃ N : ℕ, paperFourierHeightCutoff (circleMode z) N =ᵐ[circleMeasure] circleMode z) ↔
      z = 0 ∨ XiC z = 0 := by
  constructor
  · rintro ⟨N, hN⟩
    apply (memLp_top_circleMode_iff z).mp
    apply memLp_top_of_bound (measurable_circleMode_all z).aestronglyMeasurable
      (Real.exp ((2 : ℝ) ^ (N + 1)))
    filter_upwards [hN] with x hx
    rw [← hx]
    exact norm_paperFourierHeightCutoff_le _ _ _
  · intro hz
    obtain ⟨N, hN⟩ := (eventually_heightCutoff_divisor ⟨z, hz⟩).exists
    exact ⟨N, Eventually.of_forall fun x => congrFun hN x⟩

/-- The strict endpoint family never has an exact finite a.e. height cutoff. -/
theorem not_exact_heightCutoff_highTilt (z : HighTiltPoint) (N : ℕ) :
    ¬ paperFourierHeightCutoff (circleMode z.val) N =ᵐ[circleMeasure] circleMode z.val := by
  intro h
  exact not_memLp_highTilt z ((memLp_circleMode_iff_all z.val).mpr
    ((exists_exact_heightCutoff_iff z.val).mp ⟨N, h⟩))

theorem heightCutoff_highTilt_integrable (z : HighTiltPoint) (N : ℕ) :
    Integrable (paperFourierHeightCutoff (circleMode z.val) N) circleMeasure :=
  (memLLogL_highTilt z).integrable.indicator₀
    (nullMeasurableSet_lt (measurable_circleMode_all z.val).norm.aemeasurable aemeasurable_const)

/-- Proven logarithmic admission pays the actual non-L² cutoff error. -/
theorem heightCutoff_highTilt_error_le (z : HighTiltPoint) (N : ℕ) :
    (∫ x, ‖circleMode z.val x - paperFourierHeightCutoff (circleMode z.val) N x‖ ∂circleMeasure) ≤
      ((2 : ℝ) ^ (N + 1))⁻¹ *
        ∫ x, ‖circleMode z.val x‖ * Real.log (2 + ‖circleMode z.val x‖) ∂circleMeasure := by
  rw [← integral_const_mul]
  exact integral_mono
    (((memLLogL_highTilt z).integrable.sub (heightCutoff_highTilt_integrable z N)).norm)
    ((memLLogL_highTilt z).2.const_mul _)
    (norm_sub_paperFourierHeightCutoff_le _ N)

/-- Every finite height cutoff leaves positive L¹ error on a high-tilt mode. -/
theorem heightCutoff_highTilt_error_pos (z : HighTiltPoint) (N : ℕ) :
    0 < ∫ x, ‖circleMode z.val x - paperFourierHeightCutoff (circleMode z.val) N x‖
      ∂circleMeasure := by
  by_contra h
  have hz : (∫ x, ‖circleMode z.val x - paperFourierHeightCutoff (circleMode z.val) N x‖
      ∂circleMeasure) = 0 :=
    le_antisymm (not_lt.mp h) (integral_nonneg fun x => norm_nonneg _)
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg _)
    (((memLLogL_highTilt z).integrable.sub (heightCutoff_highTilt_integrable z N)).norm)).mp hz
  apply not_exact_heightCutoff_highTilt z N
  filter_upwards [ha] with x hx
  exact (sub_eq_zero.mp (norm_eq_zero.mp hx)).symm

/-- The positive finite errors nevertheless tend geometrically to zero. -/
theorem tendsto_heightCutoff_highTilt_L1 (z : HighTiltPoint) :
    Tendsto (fun N => ∫ x,
      ‖circleMode z.val x - paperFourierHeightCutoff (circleMode z.val) N x‖ ∂circleMeasure)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N => integral_nonneg fun x => norm_nonneg _)
    (heightCutoff_highTilt_error_le z)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have h : Tendsto (fun N => ((2 : ℝ) ^ (N + 1))⁻¹) atTop (𝓝 0) := by
    have he (N : ℕ) : ((2 : ℝ) ^ (N + 1))⁻¹ = ((2 : ℝ)⁻¹) ^ N * (2 : ℝ)⁻¹ := by
      rw [← inv_pow, pow_succ]
    simpa only [he, zero_mul] using hpow.mul_const ((2 : ℝ)⁻¹)
  simpa using h.mul_const
    (∫ x, ‖circleMode z.val x‖ * Real.log (2 + ‖circleMode z.val x‖) ∂circleMeasure)

end RHTower.PaperThetaEndpoint

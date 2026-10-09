import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.HeightLayers

/-!
# Paid L² admission and height truncation for the Fourier endpoint

Every actual L² circle input belongs to the upstream L log L domain. Its logarithmic mass
controls bounded height cutoffs with an explicit geometric L¹ error. The upstream height-layer
cost is summable for these inputs, with no additional integrability premise.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Filter Topology FourierLLogL
open scoped ENNReal

/-- A quadratic majorant pays the logarithmic density from L² data. -/
theorem paperOrliczDensity_le_square (z : ℂ) :
    ‖z‖ * Real.log (2 + ‖z‖) ≤ ‖z‖ + ‖z‖ ^ 2 := by
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + ‖z‖)
  nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg z)]

private theorem integrable_paperOrliczDensity
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : Lp ℂ 2 μ) :
    Integrable (fun x => ‖f x‖ * Real.log (2 + ‖f x‖)) μ := by
  have h1 : Integrable (fun x => ‖f x‖) μ :=
    ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm
  have h2 : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hn := (Lp.aestronglyMeasurable f).norm.aemeasurable
  have hm : AEStronglyMeasurable (fun x => ‖f x‖ * Real.log (2 + ‖f x‖)) μ :=
    (hn.mul ((aemeasurable_const.add hn).log)).aestronglyMeasurable
  apply (h1.add h2).mono' hm
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (orliczDensity_nonneg (f x))]
  exact paperOrliczDensity_le_square _

/-- Every L² circle input pays the endpoint theorem's actual L log L admission. -/
theorem paperMemLLogL_Lp (f : Lp ℂ 2 circleMeasure) : MemLLogL f :=
  ⟨(Lp.aestronglyMeasurable f), integrable_paperOrliczDensity circleMeasure f⟩

/-- The admission cost is bounded by the existing first and second moments. -/
theorem paperLp_orliczIntegral_le (f : Lp ℂ 2 circleMeasure) :
    (∫ x, ‖f x‖ * Real.log (2 + ‖f x‖) ∂circleMeasure) ≤
      (∫ x, ‖f x‖ ∂circleMeasure) + ∫ x, ‖f x‖ ^ 2 ∂circleMeasure := by
  have h1 : Integrable (fun x => ‖f x‖) circleMeasure :=
    ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm
  have h2 : Integrable (fun x => ‖f x‖ ^ 2) circleMeasure :=
    (Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [← integral_add h1 h2]
  exact integral_mono (paperMemLLogL_Lp f).2 (h1.add h2)
    (fun x => paperOrliczDensity_le_square (f x))

/-- The paper's entropy-sensitive height-layer cost is summable for every L² input. -/
theorem paperLp_heightLayerCost_summable (f : Lp ℂ 2 circleMeasure) :
    Summable (fun j => heightLayerMass f j *
      ((2 : ℝ) ^ (j + 2) + max 0 (-Real.log (heightLayerMass f j)))) :=
  (paperMemLLogL_Lp f).summable_heightLayerCost

/-- Retain values below the `N`th double-exponential height boundary. -/
def paperFourierHeightCutoff (f : Torus → ℂ) (N : ℕ) : Torus → ℂ :=
  {x | ‖f x‖ < Real.exp ((2 : ℝ) ^ (N + 1))}.indicator f

theorem norm_paperFourierHeightCutoff_le (f : Torus → ℂ) (N : ℕ) (x : Torus) :
    ‖paperFourierHeightCutoff f N x‖ ≤ Real.exp ((2 : ℝ) ^ (N + 1)) := by
  by_cases hx : ‖f x‖ < Real.exp ((2 : ℝ) ^ (N + 1))
  · simpa [paperFourierHeightCutoff, hx] using hx.le
  · simp [paperFourierHeightCutoff, hx, Real.exp_nonneg]

theorem paperFourierHeightCutoff_integrable (f : Lp ℂ 2 circleMeasure) (N : ℕ) :
    Integrable (paperFourierHeightCutoff f N) circleMeasure :=
  (paperMemLLogL_Lp f).integrable.indicator₀
    (nullMeasurableSet_lt (Lp.aestronglyMeasurable f).norm.aemeasurable aemeasurable_const)

/-- Pointwise tail error is paid by logarithmic mass at the reciprocal height scale. -/
theorem norm_sub_paperFourierHeightCutoff_le (f : Torus → ℂ) (N : ℕ) (x : Torus) :
    ‖f x - paperFourierHeightCutoff f N x‖ ≤
      ((2 : ℝ) ^ (N + 1))⁻¹ * (‖f x‖ * Real.log (2 + ‖f x‖)) := by
  by_cases hx : ‖f x‖ < Real.exp ((2 : ℝ) ^ (N + 1))
  · have hx' : x ∈ {y | ‖f y‖ < Real.exp ((2 : ℝ) ^ (N + 1))} := hx
    rw [paperFourierHeightCutoff, Set.indicator_of_mem hx', sub_self, norm_zero]
    exact mul_nonneg (by positivity) (orliczDensity_nonneg _)
  · have hlog : (2 : ℝ) ^ (N + 1) ≤ Real.log (2 + ‖f x‖) := by
      calc
        (2 : ℝ) ^ (N + 1) = Real.log (Real.exp ((2 : ℝ) ^ (N + 1))) :=
          (Real.log_exp _).symm
        _ ≤ Real.log (2 + ‖f x‖) := Real.log_le_log (Real.exp_pos _)
          ((le_of_not_gt hx).trans (by linarith))
    have hx' : x ∉ {y | ‖f y‖ < Real.exp ((2 : ℝ) ^ (N + 1))} := hx
    rw [paperFourierHeightCutoff, Set.indicator_of_notMem hx', sub_zero]
    have h := (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (N + 1))).mpr
      (mul_le_mul_of_nonneg_left hlog (norm_nonneg (f x)))
    simpa only [div_eq_mul_inv, mul_comm] using h

/-- The bounded cutoffs have a geometric L¹ error, paid by the input's logarithmic mass. -/
theorem paperFourierHeightCutoff_error_le (f : Lp ℂ 2 circleMeasure) (N : ℕ) :
    (∫ x, ‖f x - paperFourierHeightCutoff f N x‖ ∂circleMeasure) ≤
      ((2 : ℝ) ^ (N + 1))⁻¹ * ∫ x, ‖f x‖ * Real.log (2 + ‖f x‖) ∂circleMeasure := by
  rw [← integral_const_mul]
  apply integral_mono
    (((paperMemLLogL_Lp f).integrable.sub (paperFourierHeightCutoff_integrable f N)).norm)
    ((paperMemLLogL_Lp f).2.const_mul _)
  exact norm_sub_paperFourierHeightCutoff_le f N

/-- Every actual L² input is recovered in L¹ by the bounded height cutoffs. -/
theorem tendsto_paperFourierHeightCutoff_L1 (f : Lp ℂ 2 circleMeasure) :
    Tendsto (fun N => ∫ x, ‖f x - paperFourierHeightCutoff f N x‖ ∂circleMeasure)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N => integral_nonneg (fun x => norm_nonneg _))
    (paperFourierHeightCutoff_error_le f)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have h : Tendsto (fun N => ((2 : ℝ) ^ (N + 1))⁻¹) atTop (𝓝 0) := by
    have he (N : ℕ) : ((2 : ℝ) ^ (N + 1))⁻¹ = ((2 : ℝ)⁻¹) ^ N * (2 : ℝ)⁻¹ := by
      rw [← inv_pow, pow_succ]
    simpa only [he, zero_mul] using hpow.mul_const ((2 : ℝ)⁻¹)
  simpa using h.mul_const (∫ x, ‖f x‖ * Real.log (2 + ‖f x‖) ∂circleMeasure)

end

end GaloisForLFunctions.HTGeometry

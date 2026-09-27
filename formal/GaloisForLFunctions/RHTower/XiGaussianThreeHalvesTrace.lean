import GaloisForLFunctions.RHTower.XiGaussianThreeHalvesPhase

/-! # Independent full-trace floor with a fractional phase budget -/

open scoped Real SchwartzMap NNReal
open MeasureTheory Filter Topology GaloisForLFunctions
noncomputable section
namespace RHTower

/-- Raising the degree ceiling enlarges the fractional phase budget. -/
theorem xiGaussianThreeHalvesPhaseBudget_mono (r L : ℝ≥0) :
    Monotone (fun d : ℕ => xiGaussianThreeHalvesPhaseBudget d r L) := by
  intro d e hde
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, by positivity⟩
  have hp := mul_le_mul (gaussianStripSamplingFactor_mono 1 hde)
    (gaussianVerticalDefectSlope_mono R hde)
    (gaussianVerticalDefectSlope_nonneg _ R) (gaussianStripSamplingFactor_nonneg _ _)
  have hp2 := pow_le_pow_left₀ (mul_nonneg (gaussianStripSamplingFactor_nonneg _ _)
    (gaussianVerticalDefectSlope_nonneg _ R)) hp 2
  have hc2 := pow_le_pow_left₀ (gaussianCoordinateVerticalSlope_nonneg _ R)
    (gaussianCoordinateVerticalSlope_mono R hde) 2
  unfold xiGaussianThreeHalvesPhaseBudget
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg xiHeatThreeHalvesMass_nonneg (by positivity))
  exact add_le_add (mul_le_mul_of_nonneg_left hp2 (by positivity))
    (mul_le_mul_of_nonneg_left hc2 (by positivity))

/-- Independent total loss in the full trace floor. -/
def xiGaussianThreeHalvesTraceLoss (C h : ℝ) (d : ℕ) (r L : ℝ) : ℝ :=
  C * r * Real.sqrt ((d : ℝ) + 1) +
    (1 + 2 * (r * h) * Real.sqrt (4 * π * ((d : ℝ) + 2))) *
      verticalPolynomialGaussianDefect d (r / 2) ^ 2 +
    (r * h) * xiGaussianThreeHalvesPhaseBudget d r L

/-- The loss only increases when the degree ceiling is enlarged. -/
theorem xiGaussianThreeHalvesTraceLoss_mono (C h r L : ℝ≥0) :
    Monotone (fun d : ℕ => xiGaussianThreeHalvesTraceLoss C h d r L) := by
  intro d e hde
  have hc : (d : ℝ) ≤ (e : ℝ) := by exact_mod_cast hde
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, by positivity⟩
  have hA := Real.sqrt_le_sqrt (add_le_add hc (le_refl 1))
  have hA' := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (add_le_add hc (le_refl 2))
    (by positivity : (0 : ℝ) ≤ 4 * π))
  have hE := pow_le_pow_left₀ (verticalPolynomialGaussianDefect_nonneg d R)
    (verticalPolynomialGaussianDefect_mono R hde) 2
  have hT := xiGaussianThreeHalvesPhaseBudget_mono r L hde
  unfold xiGaussianThreeHalvesTraceLoss
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_left hA (by positivity)
    · exact mul_le_mul (add_le_add le_rfl (mul_le_mul_of_nonneg_left hA' (by positivity)))
        hE (sq_nonneg _) (by positivity)
  · exact mul_le_mul_of_nonneg_left hT (by positivity)

/-- The actual heat trace has a coefficient-uniform full-energy lower bound at every scale. -/
theorem exists_xiGaussian_trace_threeHalves_lower_bound :
    ∃ h : ℝ, 0 < h ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (P : Polynomial ℝ) (r L : {r : ℝ // 0 < r}),
        (1 / 4 - xiGaussianThreeHalvesTraceLoss C h (2 * P.natDegree) r L) *
          ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
        ((r : ℝ) * h) * xiPolynomialGaussianHeatTraceReal
          (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X)) (2 * π * (r : ℝ) ^ 2) := by
  obtain ⟨h, hh, C, hC, hfloor⟩ := exists_xiScaledEvenGaussian_relative_floor
  refine ⟨h, hh, C, hC, ?_⟩
  intro P r L
  have hK := hfloor P r
  have hD := mul_le_mul_of_nonneg_left (xiScaledEvenGaussianPhaseDebt_le_threeHalves P r L)
    (mul_pos r.property hh).le
  rw [xiScaledEvenGaussian_trace_eq_energy_sub_debt]
  unfold xiGaussianThreeHalvesTraceLoss
  nlinarith only [hK, hD]


end RHTower

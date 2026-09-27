import GaloisForLFunctions.RHTower.XiGaussianFullPhaseDebt
import GaloisForLFunctions.RHTower.XiComplexGaussianCoercivity
import GaloisForLFunctions.HTGeometry.GaussianWeightedVerticalSlope

/-!
# Independent Gaussian-norm control of the full Xi energy minus phase debt

The radius factor in weighted vertical error cancels the reciprocal-square
divisor loss. The resulting continuous degree-only budget combines with the
actual complex energy floor at every positive scale.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory Filter Topology GaloisForLFunctions
noncomputable section

namespace RHTower

/-- A continuous phase budget, independent of coefficients and without a scale denominator. -/
def xiGaussianSlopePhaseBudget (d : ℕ) (r : ℝ) : ℝ :=
  (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
    gaussianCoordinateVerticalSlope d (r / 2) ^ 2

/-- The apparent inverse-square scale singularity cancels against the linear strip error. -/
theorem xiGaussianFullPhaseBudget_le_slope (d : ℕ) (r : {r : ℝ // 0 < r}) :
    xiGaussianFullPhaseBudget d r ≤ xiGaussianSlopePhaseBudget d r := by
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩
  have hs := pow_le_pow_left₀ (gaussianCoordinateVerticalDefect_nonneg d R)
    (gaussianCoordinateVerticalDefect_le_radius_mul_slope d R) 2
  have hS : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := tsum_nonneg fun _ => by positivity
  have h := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 4 * (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) / (r : ℝ) ^ 2 by positivity)
  change xiGaussianFullPhaseBudget d r ≤ _ at h
  refine h.trans_eq ?_
  change (4 * (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) / (r : ℝ) ^ 2) *
    ((r : ℝ) / 2 * gaussianCoordinateVerticalSlope d ((r : ℝ) / 2)) ^ 2 =
    (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
      gaussianCoordinateVerticalSlope d ((r : ℝ) / 2) ^ 2
  field_simp [r.property.ne']
  ring

/-- Full debt is bounded in the complete Gaussian polynomial norm at every positive scale. -/
theorem xiScaledEvenGaussianPhaseDebt_le_slope (P : Polynomial ℝ) (r : {r : ℝ // 0 < r}) :
    xiScaledEvenGaussianPhaseDebt P r ≤ xiGaussianSlopePhaseBudget (2 * P.natDegree) r *
      ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 :=
  (xiScaledEvenGaussianPhaseDebt_le P r).trans
    (mul_le_mul_of_nonneg_right (xiGaussianFullPhaseBudget_le_slope _ r) (sq_nonneg _))

/-- Independent total loss in the full trace floor. -/
def xiGaussianTraceLoss (C h : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  C * r * Real.sqrt ((d : ℝ) + 1) +
    (1 + 2 * (r * h) * Real.sqrt (4 * π * ((d : ℝ) + 2))) *
      verticalPolynomialGaussianDefect d (r / 2) ^ 2 +
    (r * h) * xiGaussianSlopePhaseBudget d r

/-- The loss only increases when the degree ceiling is enlarged. -/
theorem xiGaussianTraceLoss_mono (C h r : ℝ≥0) :
    Monotone (fun d : ℕ => xiGaussianTraceLoss C h d r) := by
  intro d e hde
  have hc : (d : ℝ) ≤ (e : ℝ) := by exact_mod_cast hde
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, by positivity⟩
  have hA := Real.sqrt_le_sqrt (add_le_add hc (le_refl 1))
  have hA' := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (add_le_add hc (le_refl 2))
    (by positivity : (0 : ℝ) ≤ 4 * π))
  have hE := pow_le_pow_left₀ (verticalPolynomialGaussianDefect_nonneg d R)
    (verticalPolynomialGaussianDefect_mono R hde) 2
  have hT := pow_le_pow_left₀ (gaussianCoordinateVerticalSlope_nonneg d R)
    (gaussianCoordinateVerticalSlope_mono R hde) 2
  unfold xiGaussianTraceLoss xiGaussianSlopePhaseBudget
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_left hA (by positivity)
    · exact mul_le_mul (add_le_add le_rfl (mul_le_mul_of_nonneg_left hA' (by positivity)))
        hE (sq_nonneg _) (by positivity)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hT (tsum_nonneg fun _ => by positivity)

/-- The actual heat trace has a coefficient-uniform full-energy lower bound at every scale. -/
theorem exists_xiGaussian_trace_slope_lower_bound :
    ∃ h : ℝ, 0 < h ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (P : Polynomial ℝ) (r : {r : ℝ // 0 < r}),
        (1 / 4 - xiGaussianTraceLoss C h (2 * P.natDegree) r) *
          ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
        ((r : ℝ) * h) * xiPolynomialGaussianHeatTraceReal
          (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X)) (2 * π * (r : ℝ) ^ 2) := by
  obtain ⟨h, hh, C, hC, hfloor⟩ := exists_xiScaledEvenGaussian_relative_floor
  refine ⟨h, hh, C, hC, ?_⟩
  intro P r
  have hK := hfloor P r
  have hD := mul_le_mul_of_nonneg_left (xiScaledEvenGaussianPhaseDebt_le_slope P r)
    (mul_pos r.property hh).le
  rw [xiScaledEvenGaussian_trace_eq_energy_sub_debt]
  unfold xiGaussianTraceLoss
  nlinarith only [hK, hD]

/-- The complete degree-only loss vanishes at zero scale. -/
theorem xiGaussianTraceLoss_tendsto_zero (C h : ℝ) (d : ℕ) :
    Tendsto (xiGaussianTraceLoss C h d) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (xiGaussianTraceLoss C h d) := by
    unfold xiGaussianTraceLoss xiGaussianSlopePhaseBudget
    have hs := continuous_gaussianCoordinateVerticalSlope d
    unfold verticalPolynomialGaussianDefect
    fun_prop
  simpa [xiGaussianTraceLoss, verticalPolynomialGaussianDefect] using hc.tendsto 0

end RHTower

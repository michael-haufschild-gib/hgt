import GaloisForLFunctions.HTGeometry.FiniteKMSWightman
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Volume-preserving correction of an averaged rotation

Minz--Baker--Vanneste, arXiv:2608.16862, Appendix A, correct the contraction
of an averaged planar rotation by taking its phase. The exact squared-distance
defect proves optimality and uniqueness, and classifies the zero-mean exception.
Gibbs averages of the corpus's unitary phases give a concrete family of means.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GaloisForLFunctions.HilbertMetric
open _root_.HTGeometry

/-- Phase correction, choosing the identity rotation when the mean is zero. -/
def polarRotation (z : ℂ) : Circle := by
  classical
  exact if hz : z = 0 then 1 else
    ⟨z / (‖z‖ : ℂ), by
      change ‖z / (‖z‖ : ℂ) - 0‖ = 1
      rw [sub_zero, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z), div_self (norm_ne_zero_iff.mpr hz)]⟩

/-- Polar factorization holds even at a vanishing mean. -/
theorem norm_mul_polarRotation (z : ℂ) : (‖z‖ : ℂ) * (polarRotation z : ℂ) = z := by
  classical
  by_cases hz : z = 0
  · simp [polarRotation, hz]
  · simp only [polarRotation, dif_neg hz]
    field_simp [(Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))]

/-- Exact distance defect relative to the nearest rotation. -/
theorem polarRotation_distance_defect (z : ℂ) (u : Circle) :
    ‖z-(u:ℂ)‖^2 = (‖z‖-1)^2 + ‖z‖ * ‖(polarRotation z : ℂ)-(u:ℂ)‖^2 := by
  conv_lhs => rw [← norm_mul_polarRotation z]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_ofReal, Circle.normSq_coe, mul_one]
  simp only [mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- The phase correction attains the radial distance to the unit circle. -/
theorem polarRotation_distance (z : ℂ) :
    ‖z-(polarRotation z : ℂ)‖^2 = (‖z‖-1)^2 := by
  rw [polarRotation_distance_defect]
  simp

/-- No other rigid rotation is closer to the uncorrected mean. -/
theorem polarRotation_nearest (z : ℂ) (u : Circle) :
    ‖z-(polarRotation z : ℂ)‖^2 ≤ ‖z-(u:ℂ)‖^2 := by
  rw [polarRotation_distance, polarRotation_distance_defect]
  exact le_add_of_nonneg_right (mul_nonneg (norm_nonneg z) (sq_nonneg _))

/-- The closest rotation is unique except when every rotation is equally close. -/
theorem polarRotation_minimizer_iff (z : ℂ) (u : Circle) :
    ‖z-(u:ℂ)‖^2 = ‖z-(polarRotation z : ℂ)‖^2 ↔ z = 0 ∨ u = polarRotation z := by
  rw [polarRotation_distance, polarRotation_distance_defect]
  constructor
  · intro h
    have hp : ‖z‖ * ‖(polarRotation z : ℂ)-(u:ℂ)‖^2 = 0 := by linarith only [h]
    rcases mul_eq_zero.mp hp with hz | hu
    · exact Or.inl (norm_eq_zero.mp hz)
    · exact Or.inr (Circle.coe_injective
        (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hu))).symm)
  · rintro (rfl | rfl) <;> simp

/-- The corrected mean acts as an actual real linear isometry of the plane. -/
def polarRotationIsometry (z : ℂ) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv :=
    (LinearEquiv.smulOfUnit (M := ℂ) (Circle.toUnits (polarRotation z))).restrictScalars ℝ
  norm_map' w := by
    change ‖(polarRotation z : ℂ)*w‖ = ‖w‖
    rw [norm_mul, Circle.norm_coe, one_mul]

/-- Planar Lebesgue volume is preserved by the corrected mean. -/
theorem polarRotation_measurePreserving (z : ℂ) :
    MeasureTheory.MeasurePreserving (fun w : ℂ => (polarRotation z : ℂ)*w)
      MeasureTheory.volume MeasureTheory.volume :=
  (polarRotationIsometry z).measurePreserving

variable {α : Type*} [Fintype α] [Nonempty α]

/-- A Gibbs-weighted mean of rigid planar rotations. -/
def gibbsRotationMean (β : ℝ) (energy : α → ℝ) (phase : α → Circle) : ℂ :=
  ∑ a, (finiteGibbsStateWeight β energy a : ℂ) * (phase a : ℂ)

/-- The uncorrected Gibbs mean contracts every circular trajectory. -/
theorem norm_gibbsRotationMean_le_one (β : ℝ) (energy : α → ℝ) (phase : α → Circle) :
    ‖gibbsRotationMean β energy phase‖ ≤ 1 := by
  calc
    _ ≤ ∑ a, ‖(finiteGibbsStateWeight β energy a : ℂ) * (phase a : ℂ)‖ := norm_sum_le _ _
    _ = ∑ a, finiteGibbsStateWeight β energy a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (finiteGibbsStateWeight_pos β energy a)]
    _ = 1 := sum_finiteGibbsStateWeight_eq_one β energy

/-- Gibbs averaging loses precisely the radial component restored by polar correction. -/
theorem gibbsRotationMean_correction_error (β : ℝ) (energy : α → ℝ) (phase : α → Circle) :
    ‖gibbsRotationMean β energy phase -
      (polarRotation (gibbsRotationMean β energy phase) : ℂ)‖^2 =
      (1-‖gibbsRotationMean β energy phase‖)^2 := by
  rw [polarRotation_distance]
  ring

end GaloisForLFunctions.HilbertMetric

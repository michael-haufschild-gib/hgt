import GaloisForLFunctions.HilbertMetric.Geometry.FubiniStudyPotential
import GaloisForLFunctions.HTGeometry.PureStateProjectorTangentInertia

/-!
# Projective Gram energy and the affine Levi bounds

The Levi energy splits into the radial lower bound and normalized
projective Gram energy. Linear dependence characterizes lower-bound
equality; Hermitian orthogonality characterizes upper-bound equality.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric.FubiniStudy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The affine Levi numerator is tangent norm plus the existing projective Gram energy. -/
theorem levi_eq_projective_gram (z v : E) :
    levi z v = (‖v‖ ^ 2 + _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) z v) /
      denominator z ^ 2 := by
  rw [levi_formula, _root_.HTGeometry.projectiveGramTangentEnergy]
  have hd := (denominator_pos z).ne'
  field_simp [hd]
  unfold denominator
  ring

/-- Excess above the radial lower bound is precisely normalized projective Gram energy. -/
theorem levi_radial_excess (z v : E) :
    levi z v - ‖v‖ ^ 2 / denominator z ^ 2 =
      _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) z v / denominator z ^ 2 := by
  rw [levi_eq_projective_gram, add_div]
  ring

/-- The lower metric bound is strict exactly for complex-independent radial and tangent vectors. -/
theorem levi_lower_strict_iff (z v : E) :
    ‖v‖ ^ 2 / denominator z ^ 2 < levi z v ↔ LinearIndependent ℂ ![z, v] := by
  rw [← sub_pos, levi_radial_excess]
  rw [lt_div_iff₀ (sq_pos_of_pos (denominator_pos z)), zero_mul]
  exact _root_.HTGeometry.projectiveGramTangentEnergy_pos_iff_linearIndependent_pair z v

/-- The radial lower bound is attained exactly by dependent radial and tangent vectors. -/
theorem levi_lower_eq_iff (z v : E) :
    levi z v = ‖v‖ ^ 2 / denominator z ^ 2 ↔ ¬ LinearIndependent ℂ ![z, v] := by
  rw [← levi_lower_strict_iff]
  constructor
  · intro h
    rw [h]
    exact lt_irrefl _
  · intro h
    exact le_antisymm (le_of_not_gt h) (levi_lower_bound z v)

/-- The upper metric bound is attained exactly by Hermitian-orthogonal radial and tangent vectors. -/
theorem levi_upper_eq_iff (z v : E) :
    levi z v = ‖v‖ ^ 2 / denominator z ↔ inner ℂ z v = 0 := by
  rw [levi_formula]
  constructor
  · intro h
    have he : ‖inner ℂ z v‖ ^ 2 / denominator z ^ 2 = 0 := by linarith only [h]
    have hz := (div_eq_zero_iff.mp he).resolve_right
      (pow_ne_zero 2 (denominator_pos z).ne')
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h
    simp only [h, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]

#print axioms levi_eq_projective_gram
#print axioms levi_radial_excess
#print axioms levi_lower_strict_iff
#print axioms levi_lower_eq_iff
#print axioms levi_upper_eq_iff
end GaloisForLFunctions.HilbertMetric.FubiniStudy

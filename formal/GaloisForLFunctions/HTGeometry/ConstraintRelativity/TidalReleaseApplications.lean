import GaloisForLFunctions.HilbertMetric.Geometry.TidalReleaseDeformation
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ResourceFilteredRelations
import GaloisForLFunctions.HTGeometry.ProjectionMeasurementSurvival

/-!
# Tidal release in reporter and measurement geometry

The release identity of arXiv:2611.16083 separates normal acceleration from
quadratic extension in the existing reporter model. A projected initial state
with a normal kick has zero quadratic extension, but its exact quartic length
gain is the reporter tidal form. A kick along a measurement projection instead
has a sharp finite-time return boundary.
-/

noncomputable section

namespace HTGeometry.ConstraintRelativity

open GaloisForLFunctions.HilbertMetric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- The normal kick of a projected reporter state is orthogonal to that state. -/
theorem reporterRelease_null (L : Submodule ℝ H) (A : H →L[ℝ] H) (x : H) :
    inner ℝ (L.starProjection x) (Lᗮ.starProjection (A (L.starProjection x))) = 0 :=
  Submodule.inner_right_of_mem_orthogonal
    (L.starProjection_apply_mem x) (Lᗮ.starProjection_apply_mem _)

/-- The reporter tidal form is the exact quartic length gain of a normal release. -/
theorem reporterRelease_norm_sq (L : Submodule ℝ H) (A : H →L[ℝ] H) (x : H) (t : ℝ) :
    ‖tidalReleaseJet (L.starProjection x)
        (Lᗮ.starProjection (A (L.starProjection x))) t‖ ^ 2 =
      ‖L.starProjection x‖ ^ 2 + t ^ 4 / 4 * reporterTidalForm L A (L.starProjection x) := by
  rw [tidalReleaseJet_norm_sq, reporterRelease_null, mul_zero, add_zero]
  rfl

/-- Every normal release weakly lengthens the projected state. -/
theorem reporterRelease_length_nondecreasing
    (L : Submodule ℝ H) (A : H →L[ℝ] H) (x : H) (t : ℝ) :
    ‖L.starProjection x‖ ^ 2 ≤
      ‖tidalReleaseJet (L.starProjection x)
        (Lᗮ.starProjection (A (L.starProjection x))) t‖ ^ 2 := by
  rw [reporterRelease_norm_sq]
  exact le_add_of_nonneg_right
    (mul_nonneg (by positivity) (reporterTidalForm_nonneg L A _))

/-- Exact length preservation detects tangency of the generator, except at release. -/
theorem reporterRelease_length_eq_iff
    (L : Submodule ℝ H) (A : H →L[ℝ] H) (x : H) (t : ℝ) :
    ‖tidalReleaseJet (L.starProjection x)
        (Lᗮ.starProjection (A (L.starProjection x))) t‖ ^ 2 =
      ‖L.starProjection x‖ ^ 2 ↔ t = 0 ∨ A (L.starProjection x) ∈ L := by
  rw [reporterRelease_norm_sq, add_eq_left, mul_eq_zero, div_eq_zero_iff,
    pow_eq_zero_iff (by norm_num : 4 ≠ 0), reporterTidalForm_eq_zero_iff]
  norm_num

/-- An inward measurement kick has a universal quartic return law. -/
theorem measurementRelease_norm_sq (L : Submodule ℝ H) (x : H) (t : ℝ) :
    ‖tidalReleaseJet x (-L.starProjection x) t‖ ^ 2 =
      ‖x‖ ^ 2 + (t ^ 4 / 4 - t ^ 2) * ‖L.starProjection x‖ ^ 2 := by
  have hp : inner ℝ x (L.starProjection x) = ‖L.starProjection x‖ ^ 2 :=
    HTGeometry.re_inner_starProjection_eq_norm_sq L x
  rw [tidalReleaseJet_norm_sq, inner_neg_right, hp, norm_neg]
  ring

/-- Measurement survival gives exactly the quadratic coefficient of the inward kick. -/
theorem measurementRelease_born_coefficient (L : Submodule ℝ H) (x : H) (t : ℝ) :
    ‖tidalReleaseJet x (-L.starProjection x) t‖ ^ 2 = ‖x‖ ^ 2 +
      (t ^ 4 / 4 - t ^ 2) * inner ℝ x (L.starProjection x) := by
  rw [measurementRelease_norm_sq]
  congr 1
  exact congrArg (fun r : ℝ => (t ^ 4 / 4 - t ^ 2) * r)
    (HTGeometry.re_inner_starProjection_eq_norm_sq L x).symm

/-- The inward quadratic kick returns to its original length exactly at
`t²=4`, at release, or when the measured component vanishes. -/
theorem measurementRelease_length_eq_iff (L : Submodule ℝ H) (x : H) (t : ℝ) :
    ‖tidalReleaseJet x (-L.starProjection x) t‖ ^ 2 = ‖x‖ ^ 2 ↔
      t = 0 ∨ t ^ 2 = 4 ∨ L.starProjection x = 0 := by
  rw [measurementRelease_norm_sq, add_eq_left,
    show t ^ 4 / 4 - t ^ 2 = t ^ 2 * (t ^ 2 - 4) / 4 by ring]
  simp only [mul_eq_zero, div_eq_zero_iff, sq_eq_zero_iff, norm_eq_zero,
    sub_eq_zero, show (4 : ℝ) ≠ 0 by norm_num, or_false, or_assoc]

end HTGeometry.ConstraintRelativity

-- BEGIN PAPER AXIOM AUDIT
#print axioms HTGeometry.ConstraintRelativity.reporterRelease_null
#print axioms HTGeometry.ConstraintRelativity.reporterRelease_norm_sq
#print axioms HTGeometry.ConstraintRelativity.reporterRelease_length_nondecreasing
#print axioms HTGeometry.ConstraintRelativity.reporterRelease_length_eq_iff
#print axioms HTGeometry.ConstraintRelativity.measurementRelease_norm_sq
#print axioms HTGeometry.ConstraintRelativity.measurementRelease_born_coefficient
#print axioms HTGeometry.ConstraintRelativity.measurementRelease_length_eq_iff
-- END PAPER AXIOM AUDIT

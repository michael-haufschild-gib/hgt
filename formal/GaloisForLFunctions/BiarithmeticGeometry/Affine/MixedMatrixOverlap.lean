import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedCoordinateBoxVolume
import Mathlib.LinearAlgebra.Determinant

/-!
# Matrix minors as overlap certificates

Select each row either from the identity matrix or from a linear map's matrix.
The resulting determinant bounds the overlap of two independently centered
cubes. Keeping complementary identity rows turns a nonsingular minor into
a volume estimate for the full ambient space.
-/

open MeasureTheory
open scoped ENNReal Matrix BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rows selected from the identity and the transformed coordinate matrix. -/
def selectedMatrix (M : Matrix ι ι ℝ) (s : ι → ι ⊕ ι) : Matrix ι ι ℝ :=
  fun i j => Sum.elim (fun k => (1 : Matrix ι ι ℝ) k j) (fun k => M k j) (s i)

/-- Matrix row selection agrees with selection of original and transformed coordinates. -/
theorem selectedMatrix_mulVec (M : Matrix ι ι ℝ) (s : ι → ι ⊕ ι)
    (x : ι → ℝ) (i : ι) :
    (selectedMatrix M s *ᵥ x) i = Sum.elim x (M *ᵥ x) (s i) := by
  cases hs : s i with
  | inl k =>
    change (∑ j, selectedMatrix M s i j * x j) = x k
    simp only [selectedMatrix, hs, Sum.elim_inl]
    exact congrFun (Matrix.one_mulVec x) k
  | inr k =>
    change (∑ j, selectedMatrix M s i j * x j) = (M *ᵥ x) k
    simp only [selectedMatrix, hs, Sum.elim_inr]
    rfl

/-- Mixed-coordinate maps are represented by the selected matrix. -/
theorem mixed_toLin (M : Matrix ι ι ℝ) (s : ι → ι ⊕ ι) :
    mixed (Matrix.toLin' M) s = Matrix.toLin' (selectedMatrix M s) := by
  apply LinearMap.ext
  intro x
  funext i
  rw [mixed_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, selectedMatrix_mulVec]

/-- The determinant of mixed coordinates is the determinant of the selected rows. -/
theorem det_mixed_toLin (M : Matrix ι ι ℝ) (s : ι → ι ⊕ ι) :
    (mixed (Matrix.toLin' M) s).det = (selectedMatrix M s).det := by
  rw [mixed_toLin, LinearMap.det_toLin']

/-- A selected square minor controls the volume of centered-cube overlaps. -/
theorem selectedMatrix_det_mul_volume_overlap_le (M : Matrix ι ι ℝ)
    (s : ι → ι ⊕ ι) (a b : ι → ℝ) (r : ℝ) :
    ENNReal.ofReal |(selectedMatrix M s).det| *
      volume (centeredCube a r ∩ (Matrix.toLin' M) ⁻¹' centeredCube b r) ≤
        ENNReal.ofReal (2 * r) ^ Fintype.card ι := by
  simpa only [det_mixed_toLin] using
    determinant_mul_volume_centeredCube_overlap_le (Matrix.toLin' M) s a b r

#print axioms selectedMatrix_mulVec
#print axioms mixed_toLin
#print axioms det_mixed_toLin
#print axioms selectedMatrix_det_mul_volume_overlap_le

end
end GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

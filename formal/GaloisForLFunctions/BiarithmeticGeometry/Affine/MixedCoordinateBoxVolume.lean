import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedCoordinateVolume
import Mathlib.Tactic.Ring

/-!
# Mixed-coordinate bounds for independently translated boxes

A square selection of coordinates from two overlapping boxes lies in the
box with the selected endpoints. The determinant-volume bound therefore
extends to arbitrary box centers without any convex-body translation theorem.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
noncomputable section
variable {ι : Type*}

/-- Mixed coordinates select the corresponding lower and upper box endpoints. -/
theorem mixed_image_box_overlap_subset (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (s : ι → ι ⊕ ι) (a b c d : ι → ℝ) :
    mixed T s '' (Set.Icc a b ∩ T ⁻¹' Set.Icc c d) ⊆
      Set.Icc (fun i => Sum.elim a c (s i)) (fun i => Sum.elim b d (s i)) := by
  rintro _ ⟨x, hx, rfl⟩
  have hcoord (i : ι) : Sum.elim a c (s i) ≤ mixed T s x i ∧
      mixed T s x i ≤ Sum.elim b d (s i) := by
    rw [mixed_apply]
    cases s i with
    | inl j => exact ⟨hx.1.1 j, hx.1.2 j⟩
    | inr j => exact ⟨hx.2.1 j, hx.2.2 j⟩
  exact ⟨fun i => (hcoord i).1, fun i => (hcoord i).2⟩

/-- A cube of radius `r` with arbitrary coordinate center `c`. -/
def centeredCube (c : ι → ℝ) (r : ℝ) : Set (ι → ℝ) :=
  Set.Icc (fun i => c i - r) (fun i => c i + r)

variable [Fintype ι]

/-- Cube volume is independent of its center. -/
theorem volume_centeredCube (c : ι → ℝ) (r : ℝ) :
    volume (centeredCube c r) = ENNReal.ofReal (2 * r) ^ Fintype.card ι := by
  rw [centeredCube, Real.volume_Icc_pi]
  have hw (i : ι) : (c i + r) - (c i - r) = 2 * r := by ring
  simp only [hw, Finset.prod_const, Finset.card_univ]

/-- For arbitrary rectangular boxes, only the widths of selected coordinates enter. -/
theorem determinant_mul_volume_box_overlap_le (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (s : ι → ι ⊕ ι) (a b c d : ι → ℝ) :
    ENNReal.ofReal |(mixed T s).det| * volume (Set.Icc a b ∩ T ⁻¹' Set.Icc c d) ≤
      ∏ i, ENNReal.ofReal (Sum.elim b d (s i) - Sum.elim a c (s i)) := by
  calc
    _ = volume (mixed T s '' (Set.Icc a b ∩ T ⁻¹' Set.Icc c d)) :=
      (Measure.addHaar_image_linearMap volume (mixed T s) _).symm
    _ ≤ volume (Set.Icc (fun i => Sum.elim a c (s i)) (fun i => Sum.elim b d (s i))) :=
      measure_mono (mixed_image_box_overlap_subset T s a b c d)
    _ = _ := Real.volume_Icc_pi

/-- Independent translations do not change the mixed-coordinate upper bound. -/
theorem determinant_mul_volume_centeredCube_overlap_le
    (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (s : ι → ι ⊕ ι) (a b : ι → ℝ) (r : ℝ) :
    ENNReal.ofReal |(mixed T s).det| *
      volume (centeredCube a r ∩ T ⁻¹' centeredCube b r) ≤
        ENNReal.ofReal (2 * r) ^ Fintype.card ι := by
  have h := determinant_mul_volume_box_overlap_le T s
    (fun i => a i - r) (fun i => a i + r) (fun i => b i - r) (fun i => b i + r)
  have hwidth (i : ι) :
      Sum.elim (fun j => a j + r) (fun j => b j + r) (s i) -
        Sum.elim (fun j => a j - r) (fun j => b j - r) (s i) = 2 * r := by
    cases s i <;> dsimp <;> ring
  simpa only [centeredCube, hwidth, Finset.prod_const, Finset.card_univ] using h

#print axioms volume_centeredCube
#print axioms mixed_image_box_overlap_subset
#print axioms determinant_mul_volume_box_overlap_le
#print axioms determinant_mul_volume_centeredCube_overlap_le

end
end GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

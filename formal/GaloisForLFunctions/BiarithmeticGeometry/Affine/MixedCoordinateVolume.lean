import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Mixed-coordinate determinant bounds for box overlaps

A point in a cube and in a linear preimage of that cube has bounded
coordinates in both frames. Any square selection of those coordinates
therefore maps the overlap into the same cube. Its determinant bounds the
original overlap volume, including when the selected map is singular.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
noncomputable section
variable {ι : Type*}

/-- The closed coordinate cube of radius `r`; negative radii are allowed. -/
def cube (ι : Type*) (r : ℝ) : Set (ι → ℝ) :=
  Set.Icc (fun _ => -r) (fun _ => r)

/-- Cube membership is the uniform absolute coordinate bound. -/
theorem mem_cube_iff (x : ι → ℝ) (r : ℝ) :
    x ∈ cube ι r ↔ ∀ i, |x i| ≤ r := by
  constructor
  · intro hx i
    exact abs_le.mpr ⟨hx.1 i, hx.2 i⟩
  · intro hx
    exact ⟨fun i => (abs_le.mp (hx i)).1, fun i => (abs_le.mp (hx i)).2⟩

/-- A square selection of coordinates from the original and transformed vectors. -/
def mixed (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (s : ι → ι ⊕ ι) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi (fun i => Sum.elim LinearMap.proj (fun j => (LinearMap.proj j).comp T) (s i))

@[simp] theorem mixed_apply (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (s : ι → ι ⊕ ι)
    (x : ι → ℝ) (i : ι) : mixed T s x i = Sum.elim x (T x) (s i) := by
  change (Sum.elim LinearMap.proj (fun j => (LinearMap.proj j).comp T) (s i)) x = _
  cases s i <;> rfl

/-- Every chosen coordinate remains inside the common coordinate interval. -/
theorem mixed_image_overlap_subset (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (s : ι → ι ⊕ ι) (r : ℝ) :
    mixed T s '' (cube ι r ∩ T ⁻¹' cube ι r) ⊆ cube ι r := by
  rintro _ ⟨x, hx, rfl⟩
  have hcoord (i : ι) : -r ≤ mixed T s x i ∧ mixed T s x i ≤ r := by
    rw [mixed_apply]
    cases s i with
    | inl j => exact ⟨hx.1.1 j, hx.1.2 j⟩
    | inr j => exact ⟨hx.2.1 j, hx.2.2 j⟩
  exact ⟨fun i => (hcoord i).1, fun i => (hcoord i).2⟩

variable [Fintype ι]

/-- Cube volume is the product of its nonnegative side lengths. -/
theorem volume_cube (r : ℝ) :
    volume (cube ι r) = ENNReal.ofReal (2 * r) ^ Fintype.card ι := by
  rw [cube, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ]

/-- A mixed-coordinate minor controls overlap volume without an invertibility premise. -/
theorem determinant_mul_volume_overlap_le (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (s : ι → ι ⊕ ι) (r : ℝ) :
    ENNReal.ofReal |(mixed T s).det| * volume (cube ι r ∩ T ⁻¹' cube ι r) ≤
      ENNReal.ofReal (2 * r) ^ Fintype.card ι := by
  calc
    _ = volume (mixed T s '' (cube ι r ∩ T ⁻¹' cube ι r)) :=
      (Measure.addHaar_image_linearMap volume (mixed T s) _).symm
    _ ≤ volume (cube ι r) := measure_mono (mixed_image_overlap_subset T s r)
    _ = _ := volume_cube r

#print axioms mixed_image_overlap_subset
#print axioms volume_cube
#print axioms determinant_mul_volume_overlap_le

end
end GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

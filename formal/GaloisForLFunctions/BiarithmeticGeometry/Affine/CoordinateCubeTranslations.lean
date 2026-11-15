import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedCoordinateBoxVolume
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Tactic.Linarith

/-!
# Ambient translations of linear coordinate cubes

Moving the input center of a linear cube translates its image by the
image of that center. Ambient translations preserve outer volume on
arbitrary sets. These identities apply to singular linear maps as well.
-/

open MeasureTheory

namespace GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
noncomputable section
variable {ι : Type*}

/-- A centered cube bounds the absolute displacement in every scalar coordinate. -/
theorem mem_centeredCube_iff (a x : ι → ℝ) (r : ℝ) :
    x ∈ centeredCube a r ↔ ∀ i, |x i - a i| ≤ r := by
  constructor
  · intro hx i
    apply abs_le.mpr
    constructor <;> linarith only [hx.1 i, hx.2 i]
  · intro hx
    constructor
    · intro i
      have h := (abs_le.mp (hx i)).1
      linarith only [h]
    · intro i
      have h := (abs_le.mp (hx i)).2
      linarith only [h]

/-- Every coordinate cube is exactly a translation of the cube centered at zero. -/
theorem centeredCube_eq_add_image (a : ι → ℝ) (r : ℝ) :
    centeredCube a r = (fun x => a + x) '' centeredCube 0 r := by
  ext x
  constructor
  · intro hx
    refine ⟨x - a, ?_, by abel⟩
    rw [mem_centeredCube_iff] at hx ⊢
    intro i
    simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using hx i
  · rintro ⟨y, hy, rfl⟩
    rw [mem_centeredCube_iff] at hy ⊢
    intro i
    have he : (a i + y i) - a i = y i := by ring
    simpa only [Pi.add_apply, he, Pi.zero_apply, sub_zero] using hy i

/-- The image of an input-centered cube is translated by the image of its center. -/
theorem linear_image_centeredCube (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (a : ι → ℝ) (r : ℝ) :
    T '' centeredCube a r = (fun y => T a + y) '' (T '' centeredCube 0 r) := by
  rw [centeredCube_eq_add_image a r]
  simp only [Set.image_image, map_add]

/-- A linear coordinate cube followed by an arbitrary ambient translation. -/
def translatedLinearCube (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (a : ι → ℝ) (r : ℝ) : Set (ι → ℝ) :=
  (fun x => a + T x) '' centeredCube 0 r

/-- Translations in the range of the linear map can be absorbed into the input center. -/
theorem translatedLinearCube_at_image (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) (r : ℝ) :
    translatedLinearCube T (T c) r = T '' centeredCube c r := by
  simpa only [translatedLinearCube, Set.image_image] using (linear_image_centeredCube T c r).symm

variable [Fintype ι]

/-- Ambient translation preserves outer volume for every set. -/
theorem volume_add_image (a : ι → ℝ) (S : Set (ι → ℝ)) :
    volume ((fun x => a + x) '' S) = volume S := by
  have hpre (b : ι → ℝ) (U : Set (ι → ℝ)) :
      volume ((fun x => b + x) ⁻¹' U) = volume U := by
    change volume ((MeasurableEquiv.addLeft b) ⁻¹' U) = volume U
    rw [← MeasurableEquiv.map_apply, MeasurableEquiv.coe_addLeft, map_add_left_eq_self]
  have hset : (fun x => a + x) '' S = (fun x => -a + x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change -a + (a + y) ∈ S
      have he : -a + (a + y) = y := by abel
      simpa only [he] using hy
    · intro hx
      exact ⟨-a + x, hx, by abel⟩
  rw [hset, hpre]

/-- The volume of a translated linear cube is independent of its ambient center. -/
theorem volume_translatedLinearCube (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (a : ι → ℝ) (r : ℝ) :
    volume (translatedLinearCube T a r) = volume (T '' centeredCube 0 r) := by
  simpa only [translatedLinearCube, Set.image_image] using
    volume_add_image a (T '' centeredCube 0 r)

#print axioms mem_centeredCube_iff
#print axioms centeredCube_eq_add_image
#print axioms linear_image_centeredCube
#print axioms translatedLinearCube_at_image
#print axioms volume_add_image
#print axioms volume_translatedLinearCube

end
end GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

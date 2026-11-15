import GaloisForLFunctions.BiarithmeticGeometry.Affine.CoordinateCubeTranslations
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Doubling linear coordinate cubes

Uniform coordinate doubling carries radius-one cubes to radius-two cubes.
It commutes with every linear map and multiplies every overlap volume by
the exact ambient factor `2 ^ Fintype.card ι`.
-/

open MeasureTheory Matrix

namespace GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Simultaneous doubling of all ambient scalar coordinates. -/
def coordinateDouble : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  Matrix.toLin' (Matrix.diagonal (fun _ : ι => (2 : ℝ)))

theorem coordinateDouble_apply (x : ι → ℝ) (i : ι) : coordinateDouble x i = 2 * x i :=
  Matrix.mulVec_diagonal _ _ _

theorem coordinateDouble_eq_add (x : ι → ℝ) : coordinateDouble x = x + x := by
  funext i
  simp only [coordinateDouble_apply, Pi.add_apply, two_mul]

theorem coordinateDouble_injective : Function.Injective (coordinateDouble (ι := ι)) := by
  intro x y h
  funext i
  have hi := congrFun h i
  simp only [coordinateDouble_apply] at hi
  linarith only [hi]

/-- Doubling contributes exactly one factor two for each ambient scalar coordinate. -/
theorem volume_coordinateDouble_image (S : Set (ι → ℝ)) :
    volume (coordinateDouble '' S) =
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) * volume S := by
  simpa only [coordinateDouble, LinearMap.det_toLin', Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
    Measure.addHaar_image_linearMap volume (coordinateDouble (ι := ι)) S

/-- The doubled unit cube is exactly the radius-two cube. -/
theorem coordinateDouble_image_unitCube :
    coordinateDouble '' centeredCube (0 : ι → ℝ) 1 = centeredCube 0 2 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · intro i
      have hi := hx.1 i
      change (0 : ℝ) - 1 ≤ x i at hi
      change (0 : ℝ) - 2 ≤ coordinateDouble x i
      rw [coordinateDouble_apply]
      linarith only [hi]
    · intro i
      have hi := hx.2 i
      change x i ≤ (0 : ℝ) + 1 at hi
      change coordinateDouble x i ≤ (0 : ℝ) + 2
      rw [coordinateDouble_apply]
      linarith only [hi]
  · intro hy
    refine ⟨fun i => y i / 2, ⟨?_, ?_⟩, ?_⟩
    · intro i
      have hi := hy.1 i
      change (0 : ℝ) - 2 ≤ y i at hi
      change (0 : ℝ) - 1 ≤ y i / 2
      linarith only [hi]
    · intro i
      have hi := hy.2 i
      change y i ≤ (0 : ℝ) + 2 at hi
      change y i / 2 ≤ (0 : ℝ) + 1
      linarith only [hi]
    · funext i
      rw [coordinateDouble_apply]
      ring

/-- Doubling commutes with linear frames; the ambient center is halved before doubling. -/
theorem translatedLinearCube_two_eq_double_image
    (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (a : ι → ℝ) :
    translatedLinearCube T a 2 =
      coordinateDouble '' translatedLinearCube T (fun i => a i / 2) 1 := by
  unfold translatedLinearCube
  rw [← coordinateDouble_image_unitCube, Set.image_image, Set.image_image]
  congr 1
  funext x
  have hT : T (coordinateDouble x) = coordinateDouble (T x) := by
    simp only [coordinateDouble_eq_add, map_add]
  rw [hT]
  funext i
  simp only [Pi.add_apply, coordinateDouble_apply]
  ring

/-- Doubling two independently translated linear cubes has an exact overlap-volume factor. -/
theorem volume_two_translatedLinearCube_two
    (T U : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (a b : ι → ℝ) :
    volume (translatedLinearCube T a 2 ∩ translatedLinearCube U b 2) =
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) *
        volume (translatedLinearCube T (fun i => a i / 2) 1 ∩
          translatedLinearCube U (fun i => b i / 2) 1) := by
  rw [translatedLinearCube_two_eq_double_image, translatedLinearCube_two_eq_double_image,
    ← Set.image_inter coordinateDouble_injective, volume_coordinateDouble_image]

#print axioms coordinateDouble_injective
#print axioms volume_coordinateDouble_image
#print axioms coordinateDouble_image_unitCube
#print axioms translatedLinearCube_two_eq_double_image
#print axioms volume_two_translatedLinearCube_two

end
end GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

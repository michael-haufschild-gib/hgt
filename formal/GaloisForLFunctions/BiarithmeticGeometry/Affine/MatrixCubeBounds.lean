import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedCoordinateVolume
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Finite matrix bounds for cube inclusions

The sum of absolute matrix entries controls every coordinate on a cube.
A right inverse whose original and transformed coordinates satisfy these
bounds places a smaller cube inside the selected-coordinate image of an
overlap. The Haar image formula then supplies a determinant-weighted lower
volume bound.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.MatrixCubeBounds
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Sum of absolute entries, used as a uniform bound on every row sum. -/
def entryMass (M : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, |M i j|

theorem entryMass_nonneg (M : Matrix ι ι ℝ) : 0 ≤ entryMass M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem row_sum_le_entryMass (M : Matrix ι ι ℝ) (i : ι) :
    ∑ j, |M i j| ≤ entryMass M := by
  unfold entryMass
  exact Finset.single_le_sum (f := fun k => ∑ j, |M k j|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.mem_univ i)

/-- Entrywise absolute domination bounds the total entry mass. -/
theorem entryMass_le (M N : Matrix ι ι ℝ) (h : ∀ i j, |M i j| ≤ |N i j|) :
    entryMass M ≤ entryMass N :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j

/-- A positive radius simultaneously controlled by two fixed matrices. -/
def safeRadius (M N : Matrix ι ι ℝ) : ℝ := (1 + entryMass M + entryMass N)⁻¹

theorem safeRadius_pos (M N : Matrix ι ι ℝ) : 0 < safeRadius M N := by
  have hM := entryMass_nonneg M
  have hN := entryMass_nonneg N
  unfold safeRadius
  positivity

theorem safeRadius_le_one (M N : Matrix ι ι ℝ) : safeRadius M N ≤ 1 := by
  have hM := entryMass_nonneg M
  have hN := entryMass_nonneg N
  rw [safeRadius, inv_eq_one_div]
  apply (div_le_one (by positivity)).mpr
  linarith only [hM, hN]

theorem entryMass_mul_safeRadius_left (M N : Matrix ι ι ℝ) :
    entryMass M * safeRadius M N ≤ 1 := by
  have hM := entryMass_nonneg M
  have hN := entryMass_nonneg N
  rw [safeRadius, ← div_eq_mul_inv]
  apply (div_le_one (by positivity)).mpr
  linarith only [hN]

theorem entryMass_mul_safeRadius_right (M N : Matrix ι ι ℝ) :
    entryMass N * safeRadius M N ≤ 1 := by
  have hM := entryMass_nonneg M
  have hN := entryMass_nonneg N
  rw [safeRadius, ← div_eq_mul_inv]
  apply (div_le_one (by positivity)).mpr
  linarith only [hM]

/-- Every output coordinate is bounded by the entry mass times the input radius. -/
theorem abs_mulVec_le (M : Matrix ι ι ℝ) (x : ι → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hx : ∀ j, |x j| ≤ r) (i : ι) : |(M *ᵥ x) i| ≤ entryMass M * r := by
  calc
    _ ≤ ∑ j, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * r := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = (∑ j, |M i j|) * r := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (row_sum_le_entryMass M i) hr

variable [DecidableEq ι]

/-- A bounded right inverse puts a cube inside the selected-coordinate image. -/
theorem cube_subset_image_overlap (M F K : Matrix ι ι ℝ) (hFK : F * K = 1)
    (r : ℝ) (hr : 0 ≤ r) (hK : entryMass K * r ≤ 1)
    (hMK : entryMass (M * K) * r ≤ 1) :
    cube ι r ⊆ (Matrix.toLin' F) ''
      (cube ι 1 ∩ (Matrix.toLin' M) ⁻¹' cube ι 1) := by
  intro y hy
  have hy' := (mem_cube_iff y r).mp hy
  refine ⟨K *ᵥ y, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_cube_iff]
    intro i
    exact (abs_mulVec_le K y r hr hy' i).trans hK
  · change Matrix.toLin' M (K *ᵥ y) ∈ cube ι 1
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, mem_cube_iff]
    intro i
    exact (abs_mulVec_le (M * K) y r hr hy' i).trans hMK
  · rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hFK, Matrix.one_mulVec]

/-- The enclosed cube supplies a lower bound through the exact Haar image formula. -/
theorem cube_volume_le_det_mul_overlap (M F K : Matrix ι ι ℝ) (hFK : F * K = 1)
    (r : ℝ) (hr : 0 ≤ r) (hK : entryMass K * r ≤ 1)
    (hMK : entryMass (M * K) * r ≤ 1) :
    ENNReal.ofReal (2 * r) ^ Fintype.card ι ≤ ENNReal.ofReal |F.det| *
      volume (cube ι 1 ∩ (Matrix.toLin' M) ⁻¹' cube ι 1) := by
  calc
    _ = volume (cube ι r) := (volume_cube r).symm
    _ ≤ volume ((Matrix.toLin' F) ''
        (cube ι 1 ∩ (Matrix.toLin' M) ⁻¹' cube ι 1)) :=
      measure_mono (cube_subset_image_overlap M F K hFK r hr hK hMK)
    _ = _ := by rw [Measure.addHaar_image_linearMap, LinearMap.det_toLin']

#print axioms abs_mulVec_le
#print axioms cube_subset_image_overlap
#print axioms cube_volume_le_det_mul_overlap

end
end GaloisForLFunctions.BiarithmeticGeometry.MatrixCubeBounds

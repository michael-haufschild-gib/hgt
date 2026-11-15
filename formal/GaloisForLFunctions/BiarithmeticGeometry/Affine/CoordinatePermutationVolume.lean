import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedMatrixPolynomialDecay
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Coordinate permutations preserve matrix-cube overlap

Permuting scalar coordinates preserves product Lebesgue measure and every
coordinate cube after permuting its center. Intertwined matrix actions
therefore have equal overlap volumes. Simultaneous row and column
permutation is a concrete instance of this identity.
-/

open MeasureTheory Matrix
open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
noncomputable section
variable {ι : Type*}

/-- Permute scalar coordinates by precomposition. -/
def coordinatePermutation (e : Equiv.Perm ι) : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm

theorem coordinatePermutation_apply (e : Equiv.Perm ι) (x : ι → ℝ) (i : ι) :
    coordinatePermutation e x i = x (e i) := by
  rw [coordinatePermutation, MeasurableEquiv.coe_piCongrLeft]
  simpa only [e.symm_apply_apply] using
    Equiv.piCongrLeft_apply_apply (fun _ : ι => ℝ) e.symm x (e i)

theorem coordinatePermutation_sub (e : Equiv.Perm ι) (x y : ι → ℝ) :
    coordinatePermutation e (x - y) = coordinatePermutation e x - coordinatePermutation e y := by
  funext i
  simp only [coordinatePermutation_apply, Pi.sub_apply]

/-- Coordinate cubes are carried exactly to cubes with the corresponding permuted centers. -/
theorem coordinatePermutation_mem_centeredCube_iff (e : Equiv.Perm ι) (a x : ι → ℝ) (r : ℝ) :
    coordinatePermutation e x ∈ centeredCube (coordinatePermutation e a) r ↔ x ∈ centeredCube a r := by
  change ((∀ i, coordinatePermutation e a i - r ≤ coordinatePermutation e x i) ∧
    (∀ i, coordinatePermutation e x i ≤ coordinatePermutation e a i + r)) ↔
      ((∀ i, a i - r ≤ x i) ∧ (∀ i, x i ≤ a i + r))
  constructor
  · rintro ⟨hl, hu⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simpa only [coordinatePermutation_apply, e.apply_symm_apply] using hl (e.symm i)
    · simpa only [coordinatePermutation_apply, e.apply_symm_apply] using hu (e.symm i)
  · rintro ⟨hl, hu⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simpa only [coordinatePermutation_apply] using hl (e i)
    · simpa only [coordinatePermutation_apply] using hu (e i)

variable [Fintype ι]

theorem volume_preserving_coordinatePermutation (e : Equiv.Perm ι) :
    MeasurePreserving (coordinatePermutation e) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e.symm

/-- Scalar permutations preserve outer volume without any measurability premise on the set. -/
theorem volume_preimage_coordinatePermutation (e : Equiv.Perm ι) (S : Set (ι → ℝ)) :
    volume ((coordinatePermutation e) ⁻¹' S) = volume S := by
  rw [← MeasurableEquiv.map_apply, (volume_preserving_coordinatePermutation e).map_eq]

/-- Simultaneous row and column permutation intertwines the two matrix actions. -/
theorem submatrix_mulVec_coordinatePermutation (M : Matrix ι ι ℝ) (e : Equiv.Perm ι) (x : ι → ℝ) :
    M.submatrix e e *ᵥ coordinatePermutation e x = coordinatePermutation e (M *ᵥ x) := by
  funext a
  rw [coordinatePermutation_apply]
  change (∑ b, M (e a) (e b) * coordinatePermutation e x b) = ∑ b, M (e a) b * x b
  simp only [coordinatePermutation_apply]
  exact Equiv.sum_comp e (fun b => M (e a) b * x b)

variable [DecidableEq ι]

/-- Intertwining by a scalar permutation preserves the full centered-cube overlap volume. -/
theorem volume_matrixUnitOverlap_of_permutation (M N : Matrix ι ι ℝ) (e : Equiv.Perm ι)
    (h : ∀ x : ι → ℝ, N *ᵥ coordinatePermutation e x = coordinatePermutation e (M *ᵥ x))
    (a b : ι → ℝ) :
    volume (matrixUnitOverlap N (coordinatePermutation e a) (coordinatePermutation e b)) =
      volume (matrixUnitOverlap M a b) := by
  have hpre : (coordinatePermutation e) ⁻¹'
      matrixUnitOverlap N (coordinatePermutation e a) (coordinatePermutation e b) =
        matrixUnitOverlap M a b := by
    ext x
    change (coordinatePermutation e x ∈ centeredCube (coordinatePermutation e a) 1 ∧
      N *ᵥ coordinatePermutation e x ∈ centeredCube (coordinatePermutation e b) 1) ↔
        (x ∈ centeredCube a 1 ∧ M *ᵥ x ∈ centeredCube b 1)
    rw [h x, coordinatePermutation_mem_centeredCube_iff, coordinatePermutation_mem_centeredCube_iff]
  rw [← volume_preimage_coordinatePermutation e
    (matrixUnitOverlap N (coordinatePermutation e a) (coordinatePermutation e b)), hpre]

/-- Reindexing a matrix and both cube centers by the same permutation leaves overlap volume unchanged. -/
theorem volume_matrixUnitOverlap_submatrix (M : Matrix ι ι ℝ) (e : Equiv.Perm ι) (a b : ι → ℝ) :
    volume (matrixUnitOverlap (M.submatrix e e) (coordinatePermutation e a) (coordinatePermutation e b)) =
      volume (matrixUnitOverlap M a b) :=
  volume_matrixUnitOverlap_of_permutation M (M.submatrix e e) e
    (submatrix_mulVec_coordinatePermutation M e) a b

#print axioms volume_preserving_coordinatePermutation
#print axioms volume_preimage_coordinatePermutation
#print axioms coordinatePermutation_mem_centeredCube_iff
#print axioms submatrix_mulVec_coordinatePermutation
#print axioms volume_matrixUnitOverlap_of_permutation
#print axioms volume_matrixUnitOverlap_submatrix

end
end GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

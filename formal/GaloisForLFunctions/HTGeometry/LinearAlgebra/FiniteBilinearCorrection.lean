import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Finite correction against a bilinear form

A finite-dimensional subspace with nondegenerate restricted form has a unique
orthogonal representative in each affine coset. The ambient space may be
infinite-dimensional and its form may be degenerate. Inverting the restricted
map to the dual constructs the correction.

For a symmetric real form negative definite on the correction space, the
orthogonal representative uniquely maximizes the quadratic form in its coset.
Nested correction spaces give compatible representatives and increasing maxima.
This isolates the linear algebra of the vertical correction in Lemma 5.15 of
Liu, *Motivic generating functions and L-derivatives of cohomological automorphic
representations*.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry


section Field
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (B : LinearMap.BilinForm K V) (W : Submodule K V) [FiniteDimensional K W]
  (hW : (B.restrict W).Nondegenerate)

/-- The correction vector reproducing all pairings with the finite subspace. -/
def finiteBilinearCorrection : V →ₗ[K] W :=
  ((B.restrict W).toDual hW).symm.toLinearMap.comp (B.compl₂ W.subtype)

/-- Subtract the correction to obtain an orthogonal representative. -/
def finiteOrthogonalRepresentative : Module.End K V :=
  LinearMap.id - W.subtype.comp (finiteBilinearCorrection B W hW)

/-- The correction matches the original vector against every correction direction. -/
theorem finiteBilinearCorrection_pairing (x : V) (w : W) :
    B (finiteBilinearCorrection B W hW x : V) w = B x w := by
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hW)
    ((B.compl₂ W.subtype) x) w

/-- The representative differs from the original vector by its correction. -/
theorem finiteOrthogonalRepresentative_apply (x : V) :
    finiteOrthogonalRepresentative B W hW x = x - (finiteBilinearCorrection B W hW x : V) := rfl

/-- The corrected vector is orthogonal to the correction space. -/
theorem finiteOrthogonalRepresentative_pairing (x : V) (w : W) :
    B (finiteOrthogonalRepresentative B W hW x) w = 0 := by
  rw [finiteOrthogonalRepresentative_apply, map_sub, LinearMap.sub_apply,
    finiteBilinearCorrection_pairing, sub_self]

/-- Correction preserves the affine coset modulo the correction space. -/
theorem finiteOrthogonalRepresentative_sub_mem (x : V) :
    finiteOrthogonalRepresentative B W hW x - x ∈ W := by
  rw [finiteOrthogonalRepresentative_apply, sub_sub_cancel_left]
  exact W.neg_mem (finiteBilinearCorrection B W hW x).2

/-- The coset and orthogonality conditions uniquely determine the representative. -/
theorem finiteOrthogonalRepresentative_unique (x y : V) (hy : y - x ∈ W)
    (hyo : ∀ w : W, B y w = 0) : y = finiteOrthogonalRepresentative B W hW x := by
  have hd : y - finiteOrthogonalRepresentative B W hW x ∈ W := by
    have := W.sub_mem hy (finiteOrthogonalRepresentative_sub_mem B W hW x)
    simpa only [sub_sub_sub_cancel_right] using this
  have hz : (⟨y - finiteOrthogonalRepresentative B W hW x, hd⟩ : W) = 0 := by
    apply hW.1
    intro w
    change B (y - finiteOrthogonalRepresentative B W hW x) w = 0
    rw [map_sub, LinearMap.sub_apply, hyo, finiteOrthogonalRepresentative_pairing, sub_self]
  exact sub_eq_zero.mp (congrArg Subtype.val hz)

/-- Adding a correction direction does not change the corrected representative. -/
theorem finiteOrthogonalRepresentative_add_mem (x : V) (w : W) :
    finiteOrthogonalRepresentative B W hW (x + w) = finiteOrthogonalRepresentative B W hW x := by
  symm
  apply finiteOrthogonalRepresentative_unique B W hW (x + w)
  · have := W.sub_mem (finiteOrthogonalRepresentative_sub_mem B W hW x) w.2
    simpa only [sub_sub] using this
  · exact finiteOrthogonalRepresentative_pairing B W hW x

/-- The change in quadratic value is exactly the form on the difference. -/
theorem finiteOrthogonalRepresentative_energy_gap (hB : B.IsSymm) (x y : V)
    (hy : y - x ∈ W) :
    B y y = B (finiteOrthogonalRepresentative B W hW x)
      (finiteOrthogonalRepresentative B W hW x) +
      B (y - finiteOrthogonalRepresentative B W hW x)
        (y - finiteOrthogonalRepresentative B W hW x) := by
  have hd : y - finiteOrthogonalRepresentative B W hW x ∈ W := by
    have := W.sub_mem hy (finiteOrthogonalRepresentative_sub_mem B W hW x)
    simpa only [sub_sub_sub_cancel_right] using this
  have ho := finiteOrthogonalRepresentative_pairing B W hW x ⟨_, hd⟩
  have ho' := hB.eq (y - finiteOrthogonalRepresentative B W hW x)
    (finiteOrthogonalRepresentative B W hW x)
  change B (finiteOrthogonalRepresentative B W hW x)
    (y - finiteOrthogonalRepresentative B W hW x) = 0 at ho
  rw [map_sub] at ho
  simp only [map_sub, LinearMap.sub_apply] at ho' ⊢
  linear_combination 2 * ho + ho'

/-- The exact square-completion identity for a symmetric bilinear form. -/
theorem bilinear_square_completion (hB : B.IsSymm) (u x : V) :
    B u u - (2 * B u x - B x x) = B (x - u) (x - u) := by
  simp only [map_sub, LinearMap.sub_apply]
  rw [hB.eq x u]
  ring

/-- Correction by a larger space absorbs correction by a smaller space. -/
theorem finiteOrthogonalRepresentative_nested
    (Z : Submodule K V) [FiniteDimensional K Z] (hZ : (B.restrict Z).Nondegenerate)
    (hWZ : W ≤ Z) (x : V) :
    finiteOrthogonalRepresentative B Z hZ (finiteOrthogonalRepresentative B W hW x) =
      finiteOrthogonalRepresentative B Z hZ x := by
  symm
  apply finiteOrthogonalRepresentative_unique B Z hZ
  · have h := Z.sub_mem (finiteOrthogonalRepresentative_sub_mem B Z hZ x)
      (hWZ (finiteOrthogonalRepresentative_sub_mem B W hW x))
    simpa only [sub_sub_sub_cancel_right] using h
  · exact finiteOrthogonalRepresentative_pairing B Z hZ x

end Field

section Negative
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (B : LinearMap.BilinForm ℝ V) (W : Submodule ℝ V) [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
/-- Strict negativity on nonzero vectors forces nondegeneracy of the restricted form. -/
theorem restrict_nondegenerate_of_negative
    (hneg : ∀ w ∈ W, w ≠ 0 → B w w < 0) : (B.restrict W).Nondegenerate := by
  constructor
  · intro w hw
    by_contra h
    have hv : (w : V) ≠ 0 := fun he => h (Subtype.ext he)
    exact (ne_of_lt (hneg w w.2 hv)) (hw w)
  · intro w hw
    by_contra h
    have hv : (w : V) ≠ 0 := fun he => h (Subtype.ext he)
    exact (ne_of_lt (hneg w w.2 hv)) (hw w)

/-- Every other representative of a negative correction coset has smaller quadratic value. -/
theorem finiteOrthogonalRepresentative_strict_maximum (hB : B.IsSymm)
    (hneg : ∀ w ∈ W, w ≠ 0 → B w w < 0) (x y : V) (hy : y - x ∈ W)
    (hne : y ≠ finiteOrthogonalRepresentative B W (restrict_nondegenerate_of_negative B W hneg) x) :
    B y y < B (finiteOrthogonalRepresentative B W (restrict_nondegenerate_of_negative B W hneg) x)
      (finiteOrthogonalRepresentative B W (restrict_nondegenerate_of_negative B W hneg) x) := by
  let hW := restrict_nondegenerate_of_negative B W hneg
  have hd : y - finiteOrthogonalRepresentative B W hW x ∈ W := by
    have := W.sub_mem hy (finiteOrthogonalRepresentative_sub_mem B W hW x)
    simpa only [sub_sub_sub_cancel_right] using this
  rw [finiteOrthogonalRepresentative_energy_gap B W hW hB x y hy]
  have hn := hneg _ hd (sub_ne_zero.mpr hne)
  linarith only [hn]

/-- The orthogonal representative maximizes the form in its negative correction coset. -/
theorem finiteOrthogonalRepresentative_maximum (hB : B.IsSymm)
    (hneg : ∀ w ∈ W, w ≠ 0 → B w w < 0) (x y : V) (hy : y - x ∈ W) :
    B y y ≤ B (finiteOrthogonalRepresentative B W (restrict_nondegenerate_of_negative B W hneg) x)
      (finiteOrthogonalRepresentative B W (restrict_nondegenerate_of_negative B W hneg) x) := by
  by_cases h : y = finiteOrthogonalRepresentative B W (restrict_nondegenerate_of_negative B W hneg) x
  · rw [h]
  · exact (finiteOrthogonalRepresentative_strict_maximum B W hB hneg x y hy h).le

/-- Enlarging a negative correction space increases the corrected quadratic value. -/
theorem finiteOrthogonalRepresentative_energy_mono (hB : B.IsSymm)
    (Z : Submodule ℝ V) [FiniteDimensional ℝ Z] (hWZ : W ≤ Z)
    (hZneg : ∀ z ∈ Z, z ≠ 0 → B z z < 0) (x : V) :
    B (finiteOrthogonalRepresentative B W
      (restrict_nondegenerate_of_negative B W (fun w hw => hZneg w (hWZ hw))) x)
      (finiteOrthogonalRepresentative B W
      (restrict_nondegenerate_of_negative B W (fun w hw => hZneg w (hWZ hw))) x) ≤
    B (finiteOrthogonalRepresentative B Z (restrict_nondegenerate_of_negative B Z hZneg) x)
      (finiteOrthogonalRepresentative B Z (restrict_nondegenerate_of_negative B Z hZneg) x) := by
  apply finiteOrthogonalRepresentative_maximum B Z hB hZneg
  exact hWZ (finiteOrthogonalRepresentative_sub_mem B W _ x)

end Negative
end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.finiteOrthogonalRepresentative_unique
#print axioms GaloisForLFunctions.HTGeometry.finiteOrthogonalRepresentative_strict_maximum
#print axioms GaloisForLFunctions.HTGeometry.finiteOrthogonalRepresentative_nested
#print axioms GaloisForLFunctions.HTGeometry.finiteOrthogonalRepresentative_energy_mono

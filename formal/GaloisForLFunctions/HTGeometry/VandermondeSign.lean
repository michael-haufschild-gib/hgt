import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.LinearCombination

/-!
# The Vandermonde product changes by the sign under permutations

The product of all differences of a family is the Vandermonde determinant of that family, and
permuting the family permutes the rows of the Vandermonde matrix.  So the product is multiplied by
the sign of the permutation.

This is the square root of the discriminant, and the law is what makes the alternating group its
exact stabiliser.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The product of all differences of a family, in increasing order of index. -/
def vandermondeProd (v : Fin n → R) : R :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i)

theorem det_vandermonde_eq_vandermondeProd (v : Fin n → R) :
    (Matrix.vandermonde v).det = vandermondeProd v :=
  Matrix.det_vandermonde v

theorem vandermonde_comp (v : Fin n → R) (e : Equiv.Perm (Fin n)) :
    Matrix.vandermonde (v ∘ e) = (Matrix.vandermonde v).submatrix e id := by
  ext i j
  rw [Matrix.vandermonde_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply]
  rfl

/-- **The Vandermonde product changes by the sign.** -/
theorem vandermondeProd_comp (v : Fin n → R) (e : Equiv.Perm (Fin n)) :
    vandermondeProd (v ∘ e) = (Equiv.Perm.sign e : ℤ) • vandermondeProd v := by
  rw [← det_vandermonde_eq_vandermondeProd, ← det_vandermonde_eq_vandermondeProd,
    vandermonde_comp, Matrix.det_permute, zsmul_eq_mul]

/-- **The Vandermonde product is unchanged by translating the family.**  Differences do not see a
common shift. -/
theorem vandermondeProd_sub_const (v : Fin n → R) (t : R) :
    vandermondeProd (fun i => v i - t) = vandermondeProd v := by
  rw [vandermondeProd, vandermondeProd]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

/-! ## The alternating group is the exact stabiliser -/

/-- **A permutation fixes the Vandermonde product exactly when it is even**, provided the product
is nonzero and two is invertible. -/
theorem vandermondeProd_comp_eq_iff {F : Type*} [Field F] [CharZero F] {v : Fin n → F}
    (hv : vandermondeProd v ≠ 0) (e : Equiv.Perm (Fin n)) :
    vandermondeProd (v ∘ e) = vandermondeProd v ↔ e ∈ alternatingGroup (Fin n) := by
  rw [vandermondeProd_comp, Equiv.Perm.mem_alternatingGroup]
  constructor
  · intro h
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h1 | h1
    · exact h1
    · rw [h1] at h
      simp only [Units.coe_neg_one, neg_smul, one_smul] at h
      have h2 : (2 : F) * vandermondeProd v = 0 := by linear_combination -h
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd h3 (by norm_num)
      · exact absurd h3 hv
  · intro h
    rw [h]
    simp

end GaloisForLFunctions.HTGeometry

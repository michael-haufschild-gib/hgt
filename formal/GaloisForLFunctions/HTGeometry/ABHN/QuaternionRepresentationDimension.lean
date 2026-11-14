import GaloisForLFunctions.HTGeometry.LinearAlgebra.DivisionRepresentations
import Mathlib.Analysis.Quaternion

/-!
# The sharp dimension obstruction for real quaternion actions

Hamilton's division algebra acts on a finite-dimensional real vector space
exactly when its dimension is a multiple of four. This rules out actions
on nonzero spaces of dimensions one, two, or three, and constructs actions
in every allowed dimension.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped Quaternion
open LinearAlgebra

/-- A real vector space admits a quaternion representation exactly in
dimensions divisible by four. -/
theorem nonempty_realQuaternion_representation_iff
    (V : Type*) [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V] :
    Nonempty (ℍ →ₐ[ℝ] Module.End ℝ V) ↔ 4 ∣ Module.finrank ℝ V := by
  simpa only [Quaternion.finrank_eq_four] using
    (nonempty_division_representation_iff (K := ℝ) (D := ℍ) (V := V))

/-- The order of a real matrix representation of Hamilton's quaternions
is exactly a multiple of four. -/
theorem nonempty_realQuaternion_matrix_representation_iff (n : ℕ) :
    Nonempty (ℍ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ) ↔ 4 ∣ n := by
  simpa only [Quaternion.finrank_eq_four] using
    (nonempty_division_matrix_representation_iff (K := ℝ) (D := ℍ) n)

/-- No nonzero real space of dimension below four supports a quaternion
action. This is a representation obstruction, stronger than failure of
an algebra isomorphism with a matrix algebra. -/
theorem no_realQuaternion_small_representation (n : ℕ) (hn : 0 < n) (hlt : n < 4) :
    ¬ Nonempty (ℍ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ) := by
  rw [nonempty_realQuaternion_matrix_representation_iff]
  rintro ⟨k, hk⟩
  omega

/-- Every permitted matrix order occurs. -/
theorem exists_realQuaternion_matrix_representation (k : ℕ) :
    Nonempty (ℍ →ₐ[ℝ] Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ) :=
  (nonempty_realQuaternion_matrix_representation_iff _).mpr ⟨k, rfl⟩

#print axioms nonempty_realQuaternion_representation_iff
#print axioms nonempty_realQuaternion_matrix_representation_iff
#print axioms exists_realQuaternion_matrix_representation

end GaloisForLFunctions.HTGeometry.ABHN

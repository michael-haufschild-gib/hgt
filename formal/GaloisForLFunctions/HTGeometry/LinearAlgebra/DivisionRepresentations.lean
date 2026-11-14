import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Dimensions admitting a division-algebra action

A representation of a division algebra turns its underlying vector space
into a module over that division algebra. Restriction of scalars forces
divisibility of dimensions. Conversely every permitted dimension occurs,
by transporting coordinatewise multiplication on a finite free module.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra

variable {K D V : Type*} [Field K] [DivisionRing D] [Algebra K D]
  [AddCommGroup V] [Module K V]

/-- The dimension of a division algebra divides the dimension of every
space on which it acts by a unital algebra representation. -/
theorem division_dimension_dvd_of_representation (φ : D →ₐ[K] Module.End K V) :
    Module.finrank K D ∣ Module.finrank K V := by
  letI : Module D V := Module.compHom V φ.toRingHom
  letI : IsScalarTower K D V := IsScalarTower.of_algebraMap_smul fun r v => by
    change φ (algebraMap K D r) v = r • v
    rw [φ.commutes]
    rfl
  exact ⟨Module.finrank D V, (Module.finrank_mul_finrank K D V).symm⟩

/-- Dimension divisibility is also sufficient: transport the regular
action on `D^k` along a linear equivalence. -/
theorem nonempty_division_representation_iff [Module.Finite K D] [Module.Finite K V] :
    Nonempty (D →ₐ[K] Module.End K V) ↔ Module.finrank K D ∣ Module.finrank K V := by
  constructor
  · rintro ⟨φ⟩
    exact division_dimension_dvd_of_representation φ
  · rintro ⟨k, hk⟩
    have hdim : Module.finrank K (Fin k → D) = Module.finrank K V := by
      rw [← Module.finrank_mul_finrank K D (Fin k → D),
        Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ← hk]
    let e : (Fin k → D) ≃ₗ[K] V := LinearEquiv.ofFinrankEq _ _ hdim
    exact ⟨(e.conjAlgEquiv K).toAlgHom.comp (Algebra.lsmul K K (Fin k → D))⟩

/-- A finite division algebra admits a representation by square matrices
of order `n` exactly when its dimension divides `n`. -/
theorem nonempty_division_matrix_representation_iff [Module.Finite K D] (n : ℕ) :
    Nonempty (D →ₐ[K] Matrix (Fin n) (Fin n) K) ↔ Module.finrank K D ∣ n := by
  have hdim : Module.finrank K (Fin n → K) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hrep : Nonempty (D →ₐ[K] Module.End K (Fin n → K)) ↔ Module.finrank K D ∣ n := by
    simpa only [hdim] using
      (nonempty_division_representation_iff (K := K) (D := D) (V := Fin n → K))
  refine Iff.trans ?_ hrep
  constructor
  · rintro ⟨φ⟩
    exact ⟨Matrix.toLinAlgEquiv'.toAlgHom.comp φ⟩
  · rintro ⟨φ⟩
    exact ⟨Matrix.toLinAlgEquiv'.symm.toAlgHom.comp φ⟩

#print axioms nonempty_division_representation_iff
#print axioms nonempty_division_matrix_representation_iff

end GaloisForLFunctions.HTGeometry.LinearAlgebra

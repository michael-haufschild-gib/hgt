import GaloisForLFunctions.Core

/-!
# Finite selector oracle vacuity

Every predicate has a two-valued selector given by its characteristic function.  Therefore the
bare existence of a nonlinear finite-valued selector has no independent mathematical content.
-/

namespace HTGeometry

/-- Every predicate has a two-valued selector: its characteristic function. -/
theorem exists_finTwo_selector {C : Type*} (P : C → Prop) :
    ∃ S : C → Fin 2, ∃ B : Set (Fin 2), ∀ x, P x ↔ S x ∈ B := by
  classical
  let S : C → Fin 2 := fun x => if P x then 1 else 0
  refine ⟨S, {1}, ?_⟩
  intro x
  simp [S]

/-- Equivalently, every subset is the inverse image of a subset of a finite two-point type. -/
theorem exists_finTwo_preimage_eq {C : Type*} (P : Set C) :
    ∃ S : C → Fin 2, ∃ B : Set (Fin 2), S ⁻¹' B = P := by
  obtain ⟨S, B, hS⟩ := exists_finTwo_selector (fun x => x ∈ P)
  exact ⟨S, B, Set.ext fun x => (hS x).symm⟩

end HTGeometry

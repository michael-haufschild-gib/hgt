import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# Narrow finite differential-algebraic transitivity

This module isolates the three finite-family lemmas needed to construct the differential matroid.
They previously reached the matroid only through the much broader `SourceLogarithmicBoundary`
module.  Keeping them here makes the matroid dependency cone small and cache-friendly.
-/

open scoped Differential
open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Adjoining a nonempty finite family is adjoining its head and then its tail. -/
theorem differentialAdjoin_fin_succ_narrow
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {n : ℕ} (x : Fin (n + 1) → E) :
    (differentialAdjoin (differentialAdjoin F ({x 0} : Set E))
      (Set.range fun i : Fin n => x i.succ)).restrictScalars F =
        differentialAdjoin F (Set.range x) := by
  rw [differentialAdjoin, differentialAdjoin,
    IntermediateField.adjoin_adjoin_left]
  congr 1
  ext z
  constructor
  · rintro (⟨w, hw, k, rfl⟩ | ⟨w, ⟨i, rfl⟩, k, rfl⟩)
    · simp only [Set.mem_singleton_iff] at hw
      subst w
      exact ⟨x 0, ⟨0, rfl⟩, k, rfl⟩
    · exact ⟨x i.succ, ⟨i.succ, rfl⟩, k, rfl⟩
  · rintro ⟨w, ⟨i, rfl⟩, k, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Set.mem_union_left _ ⟨x 0, Set.mem_singleton _, k, rfl⟩
    · exact Set.mem_union_right _ ⟨x j.succ, ⟨j, rfl⟩, k, rfl⟩

/-- Differential algebraicity is transitive across a nonempty finite DA family. -/
theorem differentialAlgebraicOver_trans_fin_succ_narrow
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (x : Fin (n + 1) → E)
    (hx : ∀ i, DifferentialAlgebraicOver F (x i)) (y : E)
    (hy : DifferentialAlgebraicOver (differentialAdjoin F (Set.range x)) y) :
    DifferentialAlgebraicOver F y := by
  induction n generalizing F with
  | zero =>
      have hrange : Set.range x = ({x 0} : Set E) := by
        ext z
        simp only [Set.mem_range, Set.mem_singleton_iff]
        constructor
        · rintro ⟨i, rfl⟩
          exact congrArg x (Fin.eq_zero i)
        · intro hz
          exact ⟨0, hz.symm⟩
      rw [hrange] at hy
      exact differentialAlgebraicOver_trans (hx 0) hy
  | succ n ih =>
      let S := differentialAdjoin F ({x 0} : Set E)
      let tail : Fin (n + 1) → E := fun i => x i.succ
      letI : DifferentialAlgebra S E :=
        ⟨fun c => derivationClosedDifferential_apply S
          (derivationClosed_differentialAdjoin F ({x 0} : Set E)) c⟩
      have htail : ∀ i, DifferentialAlgebraicOver S (tail i) := by
        intro i
        exact differentialAlgebraicOver_mono (hx i.succ)
      have hfull := differentialAdjoin_fin_succ_narrow (F := F) (E := E) x
      have hyTail : DifferentialAlgebraicOver
          (differentialAdjoin S (Set.range tail)) y := by
        rw [← hfull] at hy
        exact hy
      have hyS : DifferentialAlgebraicOver S y := ih tail htail hyTail
      exact differentialAlgebraicOver_trans (hx 0) hyS

/-- Enlarge a differential-adjoin coefficient field inside a derivation-closed intermediate field
containing its generators. -/
theorem differentialAlgebraicOver_mono_differentialAdjoin_narrow
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E]
    {s : Set E} (B : IntermediateField F E) (hB : DerivationClosed B)
    (hs : s ⊆ B) {y : E}
    (hy : DifferentialAlgebraicOver (differentialAdjoin F s) y) :
    DifferentialAlgebraicOver B y := by
  let A := differentialAdjoin F s
  have hAB : A ≤ B := differentialAdjoin_le F hs hB
  letI : Algebra A B := (IntermediateField.inclusion hAB).toAlgebra
  haveI : IsScalarTower A B E := .of_algebraMap_eq fun _ => rfl
  exact differentialAlgebraicOver_mono hy

end

end GaloisForLFunctions.HTGeometry

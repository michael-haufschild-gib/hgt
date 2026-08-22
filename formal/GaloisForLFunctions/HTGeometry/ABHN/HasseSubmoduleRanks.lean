/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseModuleRanks

/-!
# Hasse comparison of submodule finranks

The base change of a submodule is canonically the scalar extension of its carrier.  Thus the
finrank of every fixed global submodule is preserved by completion, complementing the quotient
finrank comparison for codimension.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Field scalar extension preserves the finrank of a fixed submodule. -/
theorem submodule_finrank_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (P : Submodule K M) :
    Module.finrank L (P.baseChange L) = Module.finrank K P := by
  calc
    Module.finrank L (P.baseChange L) = Module.finrank L (L ⊗[K] P) :=
      (Submodule.toBaseChange.toLinearEquiv L P).finrank_eq.symm
    _ = Module.finrank K P := Module.finrank_baseChange

/-- A number-field submodule has the same finrank after scalar extension at every completed
place. -/
theorem numberField_submodule_finrank_completion (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (P : Submodule K M)
    (p : NumberFieldPlace K) :
    Module.finrank (completion K p) (P.baseChange (completion K p)) = Module.finrank K P :=
  submodule_finrank_baseChange (L := completion K p) P

/-- An `F(t)`-submodule has the same finrank after scalar extension at every finite and infinite
completed place. -/
theorem rationalFunction_submodule_finrank_completion (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] (P : Submodule (RatFunc F) M)
    (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p) (P.baseChange (rationalFunctionCompletion F p)) =
      Module.finrank (RatFunc F) P :=
  submodule_finrank_baseChange (L := rationalFunctionCompletion F p) P

/-- A number-field submodule has finrank `n` exactly when its extension at every completed place
has finrank `n`. -/
theorem numberField_submodule_finrank_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (P : Submodule K M) (n : ℕ) :
    Module.finrank K P = n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p) (P.baseChange (completion K p)) = n := by
  constructor
  · intro h p
    rw [numberField_submodule_finrank_completion K P p, h]
  · intro h
    rw [← numberField_submodule_finrank_completion K P (witnessPlace K)]
    exact h (witnessPlace K)

/-- An `F(t)`-submodule has finrank `n` exactly when its extension at every finite and infinite
completed place has finrank `n`. -/
theorem rationalFunction_submodule_finrank_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (P : Submodule (RatFunc F) M) (n : ℕ) :
    Module.finrank (RatFunc F) P = n ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        (P.baseChange (rationalFunctionCompletion F p)) = n := by
  constructor
  · intro h p
    rw [rationalFunction_submodule_finrank_completion F P p, h]
  · intro h
    rw [← rationalFunction_submodule_finrank_completion F P .infinite]
    exact h .infinite

/-- A prescribed number-field submodule dimension can be certified at one completion. -/
theorem numberField_submodule_finrank_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (P : Submodule K M) (n : ℕ) :
    Module.finrank K P = n ↔ ∃ p : NumberFieldPlace K,
      Module.finrank (completion K p) (P.baseChange (completion K p)) = n := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberField_submodule_finrank_completion K P (witnessPlace K)).trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberField_submodule_finrank_completion K P p).symm.trans hp

/-- A prescribed `F(t)`-submodule dimension can be certified at one completion. -/
theorem rationalFunction_submodule_finrank_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (P : Submodule (RatFunc F) M) (n : ℕ) :
    Module.finrank (RatFunc F) P = n ↔ ∃ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        (P.baseChange (rationalFunctionCompletion F p)) = n := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunction_submodule_finrank_completion F P .infinite).trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunction_submodule_finrank_completion F P p).symm.trans hp

end GaloisForLFunctions.HTGeometry.ABHN

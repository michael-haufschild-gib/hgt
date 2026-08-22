/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseFiniteness

/-!
# Hasse comparison of module finranks

Field scalar extension preserves `Module.finrank`.  Therefore the finrank of a global module
equals that of every completion.  As usual, `finrank` is zero for an infinite-dimensional module;
the equality below is an exact Lean statement, not a cardinal-rank assertion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Field scalar extension preserves the finrank of a module. -/
theorem module_finrank_tensorProduct {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    Module.finrank L (L ⊗[K] M) = Module.finrank K M :=
  Module.finrank_baseChange

/-- Every completion of a number-field module has its global finrank. -/
theorem numberField_module_finrank_completion (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (p : NumberFieldPlace K) :
    Module.finrank (completion K p) (completion K p ⊗[K] M) = Module.finrank K M :=
  module_finrank_tensorProduct (L := completion K p)

/-- Every finite or infinite completion of a rational-function-field module has its global
finrank. -/
theorem rationalFunction_module_finrank_completion (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p) (rationalFunctionCompletion F p ⊗[RatFunc F] M) =
      Module.finrank (RatFunc F) M :=
  module_finrank_tensorProduct (L := rationalFunctionCompletion F p)

/-- A number-field module has finrank `n` exactly when every completed scalar extension has
finrank `n`. -/
theorem numberField_module_finrank_eq_iff_forall_place (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (n : ℕ) :
    Module.finrank K M = n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p) (completion K p ⊗[K] M) = n := by
  constructor
  · intro h p
    rw [numberField_module_finrank_completion K p, h]
  · intro h
    rw [← numberField_module_finrank_completion K (witnessPlace K)]
    exact h (witnessPlace K)

/-- A rational-function-field module has finrank `n` exactly when every finite and infinite
completed scalar extension has finrank `n`. -/
theorem rationalFunction_module_finrank_eq_iff_forall_place (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] (n : ℕ) :
    Module.finrank (RatFunc F) M = n ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) = n := by
  constructor
  · intro h p
    rw [rationalFunction_module_finrank_completion F p, h]
  · intro h
    rw [← rationalFunction_module_finrank_completion F .infinite]
    exact h .infinite

/-- A prescribed finrank of a number-field module can be certified at one completion. -/
theorem numberField_module_finrank_eq_iff_exists_place (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (n : ℕ) :
    Module.finrank K M = n ↔ ∃ p : NumberFieldPlace K,
      Module.finrank (completion K p) (completion K p ⊗[K] M) = n := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberField_module_finrank_completion K (witnessPlace K)).trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberField_module_finrank_completion K p).symm.trans hp

/-- A prescribed finrank of an `F(t)`-module can be certified at one completion. -/
theorem rationalFunction_module_finrank_eq_iff_exists_place (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] (n : ℕ) :
    Module.finrank (RatFunc F) M = n ↔ ∃ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) = n := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunction_module_finrank_completion F .infinite).trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunction_module_finrank_completion F p).symm.trans hp

end GaloisForLFunctions.HTGeometry.ABHN

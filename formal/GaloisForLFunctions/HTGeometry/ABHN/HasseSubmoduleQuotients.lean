/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapKernels
import GaloisForLFunctions.HTGeometry.ABHN.HasseModuleRanks

/-!
# Hasse comparison of submodule quotients

Base-changing the quotient projection has kernel the base-changed submodule.  Its quotient
equivalence identifies the quotient by a local submodule with the scalar extension of the global
quotient.  Thus quotient finrank, the finite-dimensional codimension invariant, is preserved at
every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Quotienting by a base-changed submodule is the scalar extension of the original quotient. -/
noncomputable def submoduleQuotientBaseChangeEquiv {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (P : Submodule K M) :
    ((L ⊗[K] M) ⧸ (P.baseChange L)) ≃ₗ[L] (L ⊗[K] (M ⧸ P)) := by
  have hker : LinearMap.ker (P.mkQ.baseChange L) = P.baseChange L := by
    rw [← linearMap_ker_baseChange, P.ker_mkQ]
  rw [← hker]
  exact (P.mkQ.baseChange L).quotKerEquivOfSurjective
    (LinearMap.baseChange_surjective L (Submodule.mkQ_surjective P))

/-- Field scalar extension preserves the finrank of a quotient by a fixed submodule. -/
theorem submodule_quotient_finrank_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (P : Submodule K M) :
    Module.finrank L ((L ⊗[K] M) ⧸ (P.baseChange L)) = Module.finrank K (M ⧸ P) := by
  calc
    Module.finrank L ((L ⊗[K] M) ⧸ (P.baseChange L)) =
        Module.finrank L (L ⊗[K] (M ⧸ P)) :=
      (submoduleQuotientBaseChangeEquiv (L := L) P).finrank_eq
    _ = Module.finrank K (M ⧸ P) := Module.finrank_baseChange

/-- The quotient by a number-field submodule has the same finrank at every completed place. -/
theorem numberField_submodule_quotient_finrank_completion (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (P : Submodule K M) (p : NumberFieldPlace K) :
    Module.finrank (completion K p) ((completion K p ⊗[K] M) ⧸
      (P.baseChange (completion K p))) = Module.finrank K (M ⧸ P) :=
  submodule_quotient_finrank_baseChange (L := completion K p) P

/-- The quotient by an `F(t)`-submodule has the same finrank at every finite and infinite
completed place. -/
theorem rationalFunction_submodule_quotient_finrank_completion (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (P : Submodule (RatFunc F) M) (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p) ((rationalFunctionCompletion F p ⊗[RatFunc F] M) ⧸
      (P.baseChange (rationalFunctionCompletion F p))) = Module.finrank (RatFunc F) (M ⧸ P) :=
  submodule_quotient_finrank_baseChange (L := rationalFunctionCompletion F p) P

/-- The quotient by a number-field submodule has finrank `n` exactly when its quotient after
every completed scalar extension has finrank `n`. -/
theorem numberField_submodule_quotient_finrank_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (P : Submodule K M) (n : ℕ) :
    Module.finrank K (M ⧸ P) = n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p) ((completion K p ⊗[K] M) ⧸
        (P.baseChange (completion K p))) = n := by
  constructor
  · intro h p
    rw [numberField_submodule_quotient_finrank_completion K P p, h]
  · intro h
    rw [← numberField_submodule_quotient_finrank_completion K P (witnessPlace K)]
    exact h (witnessPlace K)

/-- The quotient by an `F(t)`-submodule has finrank `n` exactly when its quotient after every
finite and infinite completed scalar extension has finrank `n`. -/
theorem rationalFunction_submodule_quotient_finrank_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (P : Submodule (RatFunc F) M) (n : ℕ) :
    Module.finrank (RatFunc F) (M ⧸ P) = n ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        ((rationalFunctionCompletion F p ⊗[RatFunc F] M) ⧸
          (P.baseChange (rationalFunctionCompletion F p))) = n := by
  constructor
  · intro h p
    rw [rationalFunction_submodule_quotient_finrank_completion F P p, h]
  · intro h
    rw [← rationalFunction_submodule_quotient_finrank_completion F P .infinite]
    exact h .infinite

end GaloisForLFunctions.HTGeometry.ABHN

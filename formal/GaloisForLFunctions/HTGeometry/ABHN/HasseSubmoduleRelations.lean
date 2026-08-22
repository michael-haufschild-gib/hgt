/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearIndependence

/-!
# Hasse detection of submodule relations

Containment and equality of fixed global submodules are reflected by scalar extension to all
completions.  This supplies local–global tests for structural linear-algebra statements such as
kernel or image containment, equality of spans, and equality of fixed filtrations.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

/-- Two submodules over a number field satisfy a containment relation exactly when their scalar
extensions satisfy it at every completed place. -/
theorem numberField_submodule_le_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type v} [AddCommGroup M] [Module K M]
    (P Q : Submodule K M) :
    P ≤ Q ↔ ∀ p : NumberFieldPlace K,
      P.baseChange (completion K p) ≤ Q.baseChange (completion K p) := by
  constructor
  · intro h p
    exact Submodule.baseChange_mono (completion K p) h
  · intro h
    exact (Submodule.baseChange_le_iff).mp (h (witnessPlace K))

/-- Two submodules over a number field are equal exactly when their scalar extensions are equal
at every completed place. -/
theorem numberField_submodule_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type v} [AddCommGroup M] [Module K M]
    (P Q : Submodule K M) :
    P = Q ↔ ∀ p : NumberFieldPlace K,
      P.baseChange (completion K p) = Q.baseChange (completion K p) := by
  constructor
  · intro h p
    exact congrArg (fun T : Submodule K M ↦ T.baseChange (completion K p)) h
  · intro h
    exact Submodule.baseChange_injective (h (witnessPlace K))

/-- Two submodules over `F(t)` satisfy a containment relation exactly when their scalar extensions
satisfy it at every finite and infinite completion. -/
theorem rationalFunction_submodule_le_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type v} [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :
    P ≤ Q ↔ ∀ p : RationalFunctionPlace F,
      P.baseChange (rationalFunctionCompletion F p) ≤ Q.baseChange
        (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact Submodule.baseChange_mono (rationalFunctionCompletion F p) h
  · intro h
    exact (Submodule.baseChange_le_iff).mp (h .infinite)

/-- Two submodules over `F(t)` are equal exactly when their scalar extensions are equal at every
finite and infinite completion. -/
theorem rationalFunction_submodule_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type v} [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :
    P = Q ↔ ∀ p : RationalFunctionPlace F,
      P.baseChange (rationalFunctionCompletion F p) = Q.baseChange
        (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact congrArg (fun T : Submodule (RatFunc F) M ↦
      T.baseChange (rationalFunctionCompletion F p)) h
  · intro h
    exact Submodule.baseChange_injective (h .infinite)

/-- Containment of number-field submodules can be certified at one completion. -/
theorem numberField_submodule_le_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type v} [AddCommGroup M] [Module K M]
    (P Q : Submodule K M) :
    P ≤ Q ↔ ∃ p : NumberFieldPlace K,
      P.baseChange (completion K p) ≤ Q.baseChange (completion K p) := by
  constructor
  · intro h
    exact ⟨witnessPlace K, Submodule.baseChange_mono (completion K (witnessPlace K)) h⟩
  · rintro ⟨p, hp⟩
    exact (Submodule.baseChange_le_iff).mp hp

/-- Equality of number-field submodules can be certified at one completion. -/
theorem numberField_submodule_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type v} [AddCommGroup M] [Module K M]
    (P Q : Submodule K M) :
    P = Q ↔ ∃ p : NumberFieldPlace K,
      P.baseChange (completion K p) = Q.baseChange (completion K p) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      congrArg (fun T : Submodule K M ↦ T.baseChange (completion K (witnessPlace K))) h⟩
  · rintro ⟨p, hp⟩
    exact Submodule.baseChange_injective hp

/-- Containment of `F(t)`-submodules can be certified at one completion. -/
theorem rationalFunction_submodule_le_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type v} [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :
    P ≤ Q ↔ ∃ p : RationalFunctionPlace F,
      P.baseChange (rationalFunctionCompletion F p) ≤ Q.baseChange
        (rationalFunctionCompletion F p) := by
  constructor
  · intro h
    exact ⟨.infinite,
      Submodule.baseChange_mono (rationalFunctionCompletion F .infinite) h⟩
  · rintro ⟨p, hp⟩
    exact (Submodule.baseChange_le_iff).mp hp

/-- Equality of `F(t)`-submodules can be certified at one completion. -/
theorem rationalFunction_submodule_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type v} [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :
    P = Q ↔ ∃ p : RationalFunctionPlace F,
      P.baseChange (rationalFunctionCompletion F p) = Q.baseChange
        (rationalFunctionCompletion F p) := by
  constructor
  · intro h
    exact ⟨.infinite,
      congrArg (fun T : Submodule (RatFunc F) M ↦
        T.baseChange (rationalFunctionCompletion F .infinite)) h⟩
  · rintro ⟨p, hp⟩
    exact Submodule.baseChange_injective hp

end GaloisForLFunctions.HTGeometry.ABHN

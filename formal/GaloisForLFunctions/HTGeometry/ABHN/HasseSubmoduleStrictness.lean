/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleRelations

/-!
# Hasse detection of strict submodule containment

Faithful field scalar extension reflects both containment and equality of fixed submodules.
It therefore also reflects strict containment: a proper step in a global filtration remains a
proper step at every completion, and conversely.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- Strict containment of fixed submodules is reflected by field scalar extension. -/
theorem submodule_lt_iff_baseChange_lt {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (P Q : Submodule K M) :
    P < Q ↔ P.baseChange L < Q.baseChange L := by
  constructor
  · intro h
    refine lt_of_le_of_ne (Submodule.baseChange_mono L h.le) ?_
    intro hEq
    exact h.ne (Submodule.baseChange_injective hEq)
  · intro h
    refine lt_of_le_of_ne ((Submodule.baseChange_le_iff).mp h.le) ?_
    intro hEq
    apply h.ne
    simp [hEq]

/-- Strict containment of two number-field submodules is detected at every completed place. -/
theorem numberField_submodule_lt_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (P Q : Submodule K M) :
    P < Q ↔ ∀ p : NumberFieldPlace K,
      P.baseChange (completion K p) < Q.baseChange (completion K p) := by
  constructor
  · intro h p
    exact (submodule_lt_iff_baseChange_lt (L := completion K p) P Q).mp h
  · intro h
    exact (submodule_lt_iff_baseChange_lt (L := completion K (witnessPlace K)) P Q).mpr
      (h (witnessPlace K))

/-- Strict containment of two `F(t)`-submodules is detected at every finite and infinite
completed place. -/
theorem rationalFunction_submodule_lt_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :
    P < Q ↔ ∀ p : RationalFunctionPlace F,
      P.baseChange (rationalFunctionCompletion F p) < Q.baseChange
        (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact (submodule_lt_iff_baseChange_lt (L := rationalFunctionCompletion F p) P Q).mp h
  · intro h
    exact (submodule_lt_iff_baseChange_lt (L := rationalFunctionCompletion F .infinite) P Q).mpr
      (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN

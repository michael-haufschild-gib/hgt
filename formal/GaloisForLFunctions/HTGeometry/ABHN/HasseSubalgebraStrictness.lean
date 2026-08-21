/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubalgebraContainment

/-!
# Hasse detection of strict subalgebra containment

Strict containment between two fixed global subalgebras is preserved and reflected by scalar
extension. Thus a prescribed proper subfield or proper subalgebra relation can be checked at every
completed place. This is not a descent theorem for arbitrary local subalgebras.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Strict containment of fixed subalgebras is reflected by every field scalar extension. -/
theorem subalgebra_lt_iff_baseChange_lt {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
    (C D : Subalgebra K A) : C < D ↔ C.baseChange L < D.baseChange L := by
  constructor
  · intro h
    refine lt_of_le_of_ne ?_ ?_
    · exact (subalgebra_le_iff_baseChange_le (L := L) C D).mp h.le
    · intro hEq
      apply h.ne
      exact (subalgebra_eq_iff_baseChange_eq (L := L) C D).mpr hEq
  · intro h
    refine lt_of_le_of_ne ?_ ?_
    · exact (subalgebra_le_iff_baseChange_le (L := L) C D).mpr h.le
    · intro hEq
      apply h.ne
      exact (subalgebra_eq_iff_baseChange_eq (L := L) C D).mp hEq

/-- Fixed subalgebras of a number-field algebra are strictly contained one in another exactly
when this holds after base change at every completed place. -/
theorem numberField_subalgebra_lt_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [Ring A] [Algebra K A]
    (C D : Subalgebra K A) : C < D ↔
      ∀ p : NumberFieldPlace K, C.baseChange (completion K p) < D.baseChange (completion K p) := by
  constructor
  · intro h p
    exact (subalgebra_lt_iff_baseChange_lt (L := completion K p) C D).mp h
  · intro h
    exact (subalgebra_lt_iff_baseChange_lt (L := completion K (witnessPlace K)) C D).mpr
      (h (witnessPlace K))

/-- Fixed subalgebras of an `F(t)`-algebra are strictly contained one in another exactly when this
holds after base change at every finite and infinite completion. -/
theorem rationalFunction_subalgebra_lt_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    (C D : Subalgebra (RatFunc F) A) : C < D ↔
      ∀ p : RationalFunctionPlace F,
        C.baseChange (rationalFunctionCompletion F p) <
          D.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact (subalgebra_lt_iff_baseChange_lt (L := rationalFunctionCompletion F p) C D).mp h
  · intro h
    exact (subalgebra_lt_iff_baseChange_lt
      (L := rationalFunctionCompletion F .infinite) C D).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN

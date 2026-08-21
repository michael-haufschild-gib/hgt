/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubalgebraMembership

/-!
# Hasse detection of subalgebra containment

Containment between two fixed global subalgebras is preserved and reflected by scalar extension.
Consequently, containment can be checked at every chosen completion of a number field or rational
function field. This is a descent statement for specified subalgebras; it does not assert that
arbitrary local subalgebras descend globally.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Containment of fixed subalgebras is reflected by every field scalar extension. -/
theorem subalgebra_le_iff_baseChange_le {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
    (C D : Subalgebra K A) : C ≤ D ↔ C.baseChange L ≤ D.baseChange L := by
  constructor
  · intro h
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => exact (D.baseChange L).zero_mem
    | add x y hx hy =>
      rw [map_add]
      exact (D.baseChange L).add_mem hx hy
    | tmul l c =>
      change l ⊗ₜ[K] (c : A) ∈ D.baseChange L
      exact Subalgebra.tmul_mem_baseChange (h c.property) l
  · intro h a ha
    have hbase : 1 ⊗ₜ[K] a ∈ C.baseChange L :=
      (subalgebra_mem_baseChange_iff (L := L) C a).mp ha
    exact (subalgebra_mem_baseChange_iff (L := L) D a).mpr (h hbase)

/-- Fixed subalgebras of a number-field algebra are contained one in another exactly when that
containment holds after base change at every completed place. -/
theorem numberField_subalgebra_le_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [Ring A] [Algebra K A]
    (C D : Subalgebra K A) : C ≤ D ↔
      ∀ p : NumberFieldPlace K, C.baseChange (completion K p) ≤ D.baseChange (completion K p) := by
  constructor
  · intro h p
    exact (subalgebra_le_iff_baseChange_le (L := completion K p) C D).mp h
  · intro h
    exact (subalgebra_le_iff_baseChange_le (L := completion K (witnessPlace K)) C D).mpr
      (h (witnessPlace K))

/-- Fixed subalgebras of an `F(t)`-algebra are contained one in another exactly when that
containment holds after base change at every finite and infinite completion. -/
theorem rationalFunction_subalgebra_le_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    (C D : Subalgebra (RatFunc F) A) : C ≤ D ↔
      ∀ p : RationalFunctionPlace F,
        C.baseChange (rationalFunctionCompletion F p) ≤
          D.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact (subalgebra_le_iff_baseChange_le (L := rationalFunctionCompletion F p) C D).mp h
  · intro h
    exact (subalgebra_le_iff_baseChange_le
      (L := rationalFunctionCompletion F .infinite) C D).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN

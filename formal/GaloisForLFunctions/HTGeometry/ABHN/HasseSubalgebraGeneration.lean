/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubalgebraStrictness

/-!
# Hasse detection of subalgebra generation

A fixed global subalgebra is the whole ambient algebra precisely when its scalar extension is the
whole scalar-extended algebra. The number-field and rational-function corollaries allow this fixed
generation property to be checked at every completion. They do not assert that locally generated
algebras arise from a single global subalgebra.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Scalar extension of the full subalgebra is full. -/
theorem subalgebra_baseChange_top {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A] :
    (⊤ : Subalgebra K A).baseChange L = ⊤ := by
  apply top_unique
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact (⊤ : Subalgebra K A).baseChange L |>.zero_mem
  | add x y hx hy =>
    exact ((⊤ : Subalgebra K A).baseChange L).add_mem hx hy
  | tmul l a =>
    change l ⊗ₜ[K] a ∈ (⊤ : Subalgebra K A).baseChange L
    exact Subalgebra.tmul_mem_baseChange
      (C := (⊤ : Subalgebra K A)) (show a ∈ (⊤ : Subalgebra K A) from trivial) l

/-- A fixed subalgebra is the whole algebra exactly when every field scalar extension is whole. -/
theorem subalgebra_eq_top_iff_baseChange_eq_top {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
    (C : Subalgebra K A) : C = ⊤ ↔ C.baseChange L = ⊤ := by
  constructor
  · intro h
    rw [h]
    exact subalgebra_baseChange_top
  · intro h
    apply (subalgebra_eq_iff_baseChange_eq (L := L) C ⊤).mpr
    rw [subalgebra_baseChange_top]
    exact h

/-- A fixed subalgebra of a number-field algebra is the whole algebra exactly when it becomes
the whole algebra at every completed place. -/
theorem numberField_subalgebra_eq_top_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [Ring A] [Algebra K A]
    (C : Subalgebra K A) : C = ⊤ ↔
      ∀ p : NumberFieldPlace K, C.baseChange (completion K p) = ⊤ := by
  constructor
  · intro h p
    exact (subalgebra_eq_top_iff_baseChange_eq_top (L := completion K p) C).mp h
  · intro h
    exact (subalgebra_eq_top_iff_baseChange_eq_top
      (L := completion K (witnessPlace K)) C).mpr (h (witnessPlace K))

/-- A fixed subalgebra of an `F(t)`-algebra is the whole algebra exactly when it becomes the
whole algebra at every finite and infinite completion. -/
theorem rationalFunction_subalgebra_eq_top_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    (C : Subalgebra (RatFunc F) A) : C = ⊤ ↔
      ∀ p : RationalFunctionPlace F, C.baseChange (rationalFunctionCompletion F p) = ⊤ := by
  constructor
  · intro h p
    exact (subalgebra_eq_top_iff_baseChange_eq_top
      (L := rationalFunctionCompletion F p) C).mp h
  · intro h
    exact (subalgebra_eq_top_iff_baseChange_eq_top
      (L := rationalFunctionCompletion F .infinite) C).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN

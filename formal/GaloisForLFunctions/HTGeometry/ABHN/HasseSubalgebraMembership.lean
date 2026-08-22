/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleMembership

/-!
# Hasse detection of subalgebra membership

An element of a fixed global subalgebra remains, and is detected as, an element of its actual
base-changed subalgebra.  The completion-level corollaries apply this to every specified
subalgebra of a central simple algebra.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Membership in a subalgebra is reflected by every field scalar extension. -/
theorem subalgebra_mem_baseChange_iff {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
    (C : Subalgebra K A) (a : A) :
    a ∈ C ↔ 1 ⊗ₜ[K] a ∈ C.baseChange L := by
  constructor
  · intro ha
    exact Subalgebra.tmul_mem_baseChange ha 1
  · intro ha
    apply (submodule_mem_baseChange_iff (L := L) C.toSubmodule a).mpr
    have hle : (C.baseChange L).toSubmodule ≤ C.toSubmodule.baseChange L := by
      rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => exact (C.toSubmodule.baseChange L).zero_mem
      | add x y hx hy =>
        rw [map_add]
        exact (C.toSubmodule.baseChange L).add_mem hx hy
      | tmul l c =>
        change l ⊗ₜ[K] (c : A) ∈ C.toSubmodule.baseChange L
        exact Submodule.tmul_mem_baseChange_of_mem l c.property
    exact hle ha

/-- Two fixed subalgebras are equal exactly when their field scalar extensions are equal. -/
theorem subalgebra_eq_iff_baseChange_eq {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
    (C D : Subalgebra K A) : C = D ↔ C.baseChange L = D.baseChange L := by
  constructor
  · intro h
    rw [h]
  · intro h
    ext a
    constructor
    · intro ha
      have hbase : 1 ⊗ₜ[K] a ∈ C.baseChange L :=
        (subalgebra_mem_baseChange_iff (L := L) C a).mp ha
      rw [h] at hbase
      exact (subalgebra_mem_baseChange_iff (L := L) D a).mpr hbase
    · intro ha
      have hbase : 1 ⊗ₜ[K] a ∈ D.baseChange L :=
        (subalgebra_mem_baseChange_iff (L := L) D a).mp ha
      rw [← h] at hbase
      exact (subalgebra_mem_baseChange_iff (L := L) C a).mpr hbase

/-- Two subalgebras of a number-field algebra are equal exactly when their base changes agree at
every completed place. -/
theorem numberField_subalgebra_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [Ring A] [Algebra K A]
    (C D : Subalgebra K A) : C = D ↔
      ∀ p : NumberFieldPlace K, C.baseChange (completion K p) = D.baseChange (completion K p) := by
  constructor
  · intro h p
    rw [h]
  · intro h
    exact (subalgebra_eq_iff_baseChange_eq
      (L := completion K (witnessPlace K)) C D).mpr (h (witnessPlace K))

/-- Two subalgebras of an `F(t)`-algebra are equal exactly when their base changes agree at every
finite and infinite completed place. -/
theorem rationalFunction_subalgebra_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    (C D : Subalgebra (RatFunc F) A) : C = D ↔
      ∀ p : RationalFunctionPlace F,
        C.baseChange (rationalFunctionCompletion F p) =
          D.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    rw [h]
  · intro h
    exact (subalgebra_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F .infinite) C D).mpr (h .infinite)

/-- A central-simple-algebra element belongs to a fixed subalgebra exactly when its scalar
extension belongs to the base-changed subalgebra. -/
theorem scalarExtensionMap_mem_subalgebraBaseChange_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K)
    (C : Subalgebra K A.carrier) (a : A.carrier) :
    a ∈ C ↔ scalarExtensionMap (L := L) A a ∈ C.baseChange L := by
  simpa only [scalarExtensionMap, Algebra.TensorProduct.includeRight_apply] using
    (subalgebra_mem_baseChange_iff (L := L) C a)

/-- A central-simple-algebra element over a number field belongs to a fixed subalgebra exactly
when its local image belongs to the base-changed subalgebra at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_mem_subalgebraBaseChange_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (C : Subalgebra K A.carrier) (a : A.carrier) :
    a ∈ C ↔ ∀ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a ∈ C.baseChange (completion K p) := by
  constructor
  · intro ha p
    exact (scalarExtensionMap_mem_subalgebraBaseChange_iff
      (K := K) (L := completion K p) A C a).mp ha
  · intro h
    exact (scalarExtensionMap_mem_subalgebraBaseChange_iff
      (K := K) (L := completion K (witnessPlace K)) A C a).mpr (h (witnessPlace K))

/-- A central-simple-algebra element over `F(t)` belongs to a fixed subalgebra exactly when its
local image belongs to the base-changed subalgebra at every finite and infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mem_subalgebraBaseChange_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (C : Subalgebra (RatFunc F) A.carrier) (a : A.carrier) :
    a ∈ C ↔ ∀ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a ∈
        C.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro ha p
    exact (scalarExtensionMap_mem_subalgebraBaseChange_iff
      (K := RatFunc F) (L := rationalFunctionCompletion F p) A C a).mp ha
  · intro h
    exact (scalarExtensionMap_mem_subalgebraBaseChange_iff
      (K := RatFunc F) (L := rationalFunctionCompletion F .infinite) A C a).mpr (h .infinite)

/-- Membership of an element in a fixed number-field subalgebra is certified at one completion. -/
theorem numberFieldLocalScalarExtensionMap_mem_subalgebraBaseChange_iff_exists_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (C : Subalgebra K A.carrier) (a : A.carrier) :
    a ∈ C ↔ ∃ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a ∈ C.baseChange (completion K p) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_mem_subalgebraBaseChange_iff
        (K := K) (L := completion K (witnessPlace K)) A C a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_mem_subalgebraBaseChange_iff
      (K := K) (L := completion K p) A C a).mpr hp

/-- Membership of an element in a fixed `F(t)`-subalgebra is certified at one completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mem_subalgebraBaseChange_iff_exists_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (C : Subalgebra (RatFunc F) A.carrier) (a : A.carrier) :
    a ∈ C ↔ ∃ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a ∈
        C.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_mem_subalgebraBaseChange_iff
        (K := RatFunc F) (L := rationalFunctionCompletion F .infinite) A C a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_mem_subalgebraBaseChange_iff
      (K := RatFunc F) (L := rationalFunctionCompletion F p) A C a).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN

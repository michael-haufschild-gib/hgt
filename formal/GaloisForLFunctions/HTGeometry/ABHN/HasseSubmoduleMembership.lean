/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalScalarExtension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Hasse detection of submodule membership

A global vector belongs to a fixed linear subobject exactly when its image belongs to the scalar
extension of that subobject.  For number fields and rational function fields, this gives a
completion-wise Hasse test for every fixed linear constraint on a central simple algebra.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Membership in a submodule is reflected by every field scalar extension. -/
theorem submodule_mem_baseChange_iff {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (P : Submodule K M) (m : M) :
    m ∈ P ↔ 1 ⊗ₜ[K] m ∈ P.baseChange L := by
  constructor
  · intro hm
    exact Submodule.tmul_mem_baseChange_of_mem 1 hm
  · intro hm
    have hle : (Submodule.span K {m}).baseChange L ≤ P.baseChange L := by
      rw [Submodule.baseChange_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxm : x = m := by simpa using hx
      subst x
      exact hm
    have hglobal : Submodule.span K {m} ≤ P := (Submodule.baseChange_le_iff).mp hle
    exact hglobal (Submodule.subset_span (by simp))

/-- A central-simple-algebra element satisfies a fixed linear constraint exactly when its scalar
extension satisfies the base-changed constraint. -/
theorem scalarExtensionMap_mem_baseChange_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K)
    (P : Submodule K A.carrier) (a : A.carrier) :
    a ∈ P ↔ scalarExtensionMap (L := L) A a ∈ P.baseChange L := by
  simpa only [scalarExtensionMap, Algebra.TensorProduct.includeRight_apply] using
    (submodule_mem_baseChange_iff (L := L) P a)

/-- A central-simple-algebra element over a number field satisfies a fixed linear constraint
exactly when it satisfies the base-changed constraint at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_mem_baseChange_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (P : Submodule K A.carrier) (a : A.carrier) :
    a ∈ P ↔ ∀ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a ∈ P.baseChange (completion K p) := by
  constructor
  · intro ha p
    exact (scalarExtensionMap_mem_baseChange_iff (K := K) (L := completion K p) A P a).mp ha
  · intro h
    exact (scalarExtensionMap_mem_baseChange_iff
      (K := K) (L := completion K (witnessPlace K)) A P a).mpr (h (witnessPlace K))

/-- A central-simple-algebra element over `F(t)` satisfies a fixed linear constraint exactly when
it satisfies the base-changed constraint at every finite and infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mem_baseChange_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (P : Submodule (RatFunc F) A.carrier) (a : A.carrier) :
    a ∈ P ↔ ∀ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a ∈
        P.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro ha p
    exact (scalarExtensionMap_mem_baseChange_iff
      (K := RatFunc F) (L := rationalFunctionCompletion F p) A P a).mp ha
  · intro h
    exact (scalarExtensionMap_mem_baseChange_iff
      (K := RatFunc F) (L := rationalFunctionCompletion F .infinite) A P a).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN

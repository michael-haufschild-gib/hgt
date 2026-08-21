/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapKernels

/-!
# Hasse detection for nonzero kernels and specified eigenvectors

Faithfully flat scalar extension reflects whether a linear map has a nontrivial kernel.  Applied
to `f - a • id`, this detects whether a specified global scalar is an eigenvalue.  The scalar is
fixed globally; this does not claim descent of independently chosen local eigenvalues.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

/-- A linear map has a nontrivial kernel exactly when any field scalar extension does. -/
theorem linearMap_ker_ne_bot_iff_baseChange {K : Type u} {L : Type v} {M : Type w} {N : Type x}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    LinearMap.ker f ≠ ⊥ ↔ LinearMap.ker (f.baseChange L) ≠ ⊥ := by
  rw [← linearMap_ker_baseChange]
  constructor
  · intro h hlocal
    apply h
    apply Submodule.baseChange_injective (A := L)
    rw [hlocal, Submodule.baseChange_bot]
  · intro h hlocal
    apply h
    rw [hlocal, Submodule.baseChange_bot]

/-- A linear map over a number field has a nontrivial kernel exactly when every completed scalar
extension does. -/
theorem numberField_linearMap_ker_ne_bot_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    LinearMap.ker f ≠ ⊥ ↔ ∀ p : NumberFieldPlace K,
      LinearMap.ker (f.baseChange (completion K p)) ≠ ⊥ := by
  constructor
  · intro h p
    exact (linearMap_ker_ne_bot_iff_baseChange (L := completion K p) f).mp h
  · intro h
    exact (linearMap_ker_ne_bot_iff_baseChange
      (L := completion K (witnessPlace K)) f).mpr (h (witnessPlace K))

/-- A linear map over `F(t)` has a nontrivial kernel exactly when every finite and infinite
completed scalar extension does. -/
theorem rationalFunction_linearMap_ker_ne_bot_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) :
    LinearMap.ker f ≠ ⊥ ↔ ∀ p : RationalFunctionPlace F,
      LinearMap.ker (f.baseChange (rationalFunctionCompletion F p)) ≠ ⊥ := by
  constructor
  · intro h p
    exact (linearMap_ker_ne_bot_iff_baseChange
      (L := rationalFunctionCompletion F p) f).mp h
  · intro h
    exact (linearMap_ker_ne_bot_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) f).mpr (h .infinite)

/-- A specified scalar is an eigenvalue of a linear endomorphism exactly when it remains an
eigenvalue after any field scalar extension. -/
theorem linearMap_eigenKernel_ne_bot_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (a : K) :
    LinearMap.ker (f - a • LinearMap.id) ≠ ⊥ ↔
      LinearMap.ker (f.baseChange L - (algebraMap K L a) • LinearMap.id) ≠ ⊥ := by
  have hbase : (f - a • LinearMap.id).baseChange L =
      f.baseChange L - (algebraMap K L a) • LinearMap.id := by
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id]
    ext x
    simp [Algebra.smul_def]
  rw [← hbase]
  exact linearMap_ker_ne_bot_iff_baseChange (L := L) (f - a • LinearMap.id)

/-- A specified scalar is an eigenvalue of an endomorphism over a number field exactly when it
is an eigenvalue after scalar extension at every completed place. -/
theorem numberField_linearMap_eigenKernel_ne_bot_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (a : K) :
    LinearMap.ker (f - a • LinearMap.id) ≠ ⊥ ↔ ∀ p : NumberFieldPlace K,
      LinearMap.ker (f.baseChange (completion K p) - (algebraMap K (completion K p) a) •
        LinearMap.id) ≠ ⊥ := by
  constructor
  · intro h p
    exact (linearMap_eigenKernel_ne_bot_iff_baseChange (L := completion K p) f a).mp h
  · intro h
    exact (linearMap_eigenKernel_ne_bot_iff_baseChange
      (L := completion K (witnessPlace K)) f a).mpr (h (witnessPlace K))

/-- A specified rational function is an eigenvalue of an endomorphism over `F(t)` exactly when it
is an eigenvalue after scalar extension at every finite and infinite completed place. -/
theorem rationalFunction_linearMap_eigenKernel_ne_bot_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :
    LinearMap.ker (f - a • LinearMap.id) ≠ ⊥ ↔ ∀ p : RationalFunctionPlace F,
      LinearMap.ker (f.baseChange (rationalFunctionCompletion F p) -
        (algebraMap (RatFunc F) (rationalFunctionCompletion F p) a) • LinearMap.id) ≠ ⊥ := by
  constructor
  · intro h p
    exact (linearMap_eigenKernel_ne_bot_iff_baseChange
      (L := rationalFunctionCompletion F p) f a).mp h
  · intro h
    exact (linearMap_eigenKernel_ne_bot_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) f a).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN

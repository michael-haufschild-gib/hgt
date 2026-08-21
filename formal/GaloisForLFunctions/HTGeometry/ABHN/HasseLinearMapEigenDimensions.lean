/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEigenvectors

/-!
# Hasse comparison of generalized eigenspace dimensions

For a fixed global scalar, scalar extension commutes with every power of `f - a • id`.
The finrank of its kernel, hence the dimension of the associated generalized eigenspace, is
therefore invariant under completion.  This does not assert descent of arbitrary local eigenvalues.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Field scalar extension preserves the finrank of every generalized eigenspace for a specified
global scalar. -/
theorem linearMap_generalizedEigenKernel_finrank_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (a : K) (n : ℕ) :
    Module.finrank L (LinearMap.ker
      ((f.baseChange L - (algebraMap K L a) • LinearMap.id) ^ n)) =
      Module.finrank K (LinearMap.ker ((f - a • LinearMap.id) ^ n)) := by
  have hbaseOne : (f - a • LinearMap.id).baseChange L =
      f.baseChange L - (algebraMap K L a) • LinearMap.id := by
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id]
    ext x
    simp [Algebra.smul_def]
  have hbase : ((f - a • LinearMap.id) ^ n).baseChange L =
      (f.baseChange L - (algebraMap K L a) • LinearMap.id) ^ n := by
    rw [LinearMap.baseChange_pow, hbaseOne]
  rw [← hbase]
  exact linearMap_ker_finrank_baseChange (L := L) ((f - a • LinearMap.id) ^ n)

/-- A specified generalized eigenspace of a number-field endomorphism has the same finrank at
every completed place. -/
theorem numberField_linearMap_generalizedEigenKernel_finrank_completion (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (a : K) (n : ℕ) (p : NumberFieldPlace K) :
    Module.finrank (completion K p) (LinearMap.ker
      ((f.baseChange (completion K p) - (algebraMap K (completion K p) a) • LinearMap.id) ^ n)) =
      Module.finrank K (LinearMap.ker ((f - a • LinearMap.id) ^ n)) :=
  linearMap_generalizedEigenKernel_finrank_baseChange (L := completion K p) f a n

/-- A specified generalized eigenspace of an `F(t)`-endomorphism has the same finrank at every
finite and infinite completed place. -/
theorem rationalFunction_linearMap_generalizedEigenKernel_finrank_completion (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) (n : ℕ) (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
      ((f.baseChange (rationalFunctionCompletion F p) -
        (algebraMap (RatFunc F) (rationalFunctionCompletion F p) a) • LinearMap.id) ^ n)) =
      Module.finrank (RatFunc F) (LinearMap.ker ((f - a • LinearMap.id) ^ n)) :=
  linearMap_generalizedEigenKernel_finrank_baseChange
    (L := rationalFunctionCompletion F p) f a n

/-- A specified generalized eigenspace of a number-field endomorphism has finrank `d` exactly
when every completed scalar extension has finrank `d`. -/
theorem numberField_linearMap_generalizedEigenKernel_finrank_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (a : K) (n d : ℕ) :
    Module.finrank K (LinearMap.ker ((f - a • LinearMap.id) ^ n)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((f.baseChange (completion K p) - (algebraMap K (completion K p) a) • LinearMap.id) ^ n)) = d := by
  constructor
  · intro h p
    rw [numberField_linearMap_generalizedEigenKernel_finrank_completion K f a n p, h]
  · intro h
    rw [← numberField_linearMap_generalizedEigenKernel_finrank_completion
      K f a n (witnessPlace K)]
    exact h (witnessPlace K)

/-- A specified generalized eigenspace of an `F(t)`-endomorphism has finrank `d` exactly when
every finite and infinite completed scalar extension has finrank `d`. -/
theorem rationalFunction_linearMap_generalizedEigenKernel_finrank_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker ((f - a • LinearMap.id) ^ n)) = d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
          ((f.baseChange (rationalFunctionCompletion F p) -
            (algebraMap (RatFunc F) (rationalFunctionCompletion F p) a) • LinearMap.id) ^ n)) = d := by
  constructor
  · intro h p
    rw [rationalFunction_linearMap_generalizedEigenKernel_finrank_completion F f a n p, h]
  · intro h
    rw [← rationalFunction_linearMap_generalizedEigenKernel_finrank_completion
      F f a n .infinite]
    exact h .infinite

end GaloisForLFunctions.HTGeometry.ABHN

import GaloisForLFunctions.Bottcher.ConnectedRepellingPeriodicAvoidance
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CompositionCokernel

/-!
# Exceptional scalar factors and operator kernels

Multiplying an operator by the finite-set exceptional polynomial preserves
its kernel off the prescribed set and kills the operator on that set.
This is the scalar-factor mechanism of Zehavi, Corollary 2.22,
arXiv:2611.18218, applied to the dynamical exceptional polynomial.
-/

noncomputable section

namespace Bottcher

open GaloisForLFunctions.RepresentationLifting.OperatorKernels
open Polynomial

variable {V U W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

/-- An exceptional polynomial has no roots beyond its prescribed finite set. -/
theorem exceptionalPoly_eval_eq_zero_iff (E : Finset ℂ) (z : ℂ) :
    (exceptionalPoly E).eval z = 0 ↔ z ∈ E := by
  classical
  simp only [exceptionalPoly, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff,
    sub_eq_zero]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Scalar removal at every parameter, including the exact exceptional behaviour. -/
theorem exceptionalPoly_operator_kernel (E : Finset ℂ) (z : ℂ) (T : V →ₗ[ℂ] U) :
    LinearMap.ker ((exceptionalPoly E).eval z • T) =
      if z ∈ E then ⊤ else T.ker := by
  classical
  by_cases hz : z ∈ E
  · rw [if_pos hz, (exceptionalPoly_eval_eq_zero_iff E z).mpr hz, zero_smul,
      LinearMap.ker_zero]
  · rw [if_neg hz]
    have hc : (exceptionalPoly E).eval z ≠ 0 :=
      fun h => hz ((exceptionalPoly_eval_eq_zero_iff E z).mp h)
    ext v
    change (exceptionalPoly E).eval z • T v = 0 ↔ T v = 0
    simp only [smul_eq_zero, hc, false_or]

/-- The operator quotient jumps to its full dimension exactly on the prescribed scalar locus. -/
theorem exceptionalPoly_observation_defect [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (E : Finset ℂ) (z : ℂ) (T : V →ₗ[ℂ] U) :
    Module.finrank ℂ ((V →ₗ[ℂ] W) ⧸
      (precompose (W := W) ((exceptionalPoly E).eval z • T)).range) =
      if z ∈ E then Module.finrank ℂ W * Module.finrank ℂ V
      else Module.finrank ℂ W * Module.finrank ℂ T.ker := by
  classical
  rw [finrank_compositionCokernel, exceptionalPoly_operator_kernel]
  split_ifs <;> simp only [finrank_top]

/-- There are only finitely many parameters at which scalar removal can change the kernel. -/
theorem exceptionalPoly_kernel_changes_finite (E : Finset ℂ) (T : V →ₗ[ℂ] U) :
    Set.Finite {z | LinearMap.ker ((exceptionalPoly E).eval z • T) ≠ T.ker} := by
  apply E.finite_toSet.subset
  intro z hz
  by_contra h
  exact hz (by rw [exceptionalPoly_operator_kernel, if_neg h])

end Bottcher

#print axioms Bottcher.exceptionalPoly_eval_eq_zero_iff
#print axioms Bottcher.exceptionalPoly_operator_kernel
#print axioms Bottcher.exceptionalPoly_observation_defect
#print axioms Bottcher.exceptionalPoly_kernel_changes_finite

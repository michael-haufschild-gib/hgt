import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticRigidity
import GaloisForLFunctions.RHTower.CompleteStripRealCoronaCompactification

/-!
# Positive-degree self-dual completions have nonsmooth Real corona

This module removes zero-set infinitude from the input of the universal P3 theorem.  A completed
self-dual function is specified by the analytic consequences supplied by positive automorphic
degree: entire differentiability, a subquadratic order envelope, growth on the positive real ray
beating every linear exponential, critical-strip confinement, and functional-equation reflection.

Finite-zero subquadratic rigidity proves infinitely many distinct zeros.  Isolated-zero theory
proves local finiteness.  The resulting complete-strip reflection divisor therefore falls under
the endpoint-holomorphic crossed-product classification, and its Real-corona idempotent is not
smooth.  No zero-counting asymptotic is assumed.
-/

noncomputable section

open Complex Filter Metric Set

namespace GaloisForLFunctions.RHTower

/-- Minimal analytic interface for a positive-degree self-dual completed `L`-function.  The
`superlinearRay` field is the analytic signature of positive degree used to exclude a finite
Hadamard divisor; zero infinitude itself is deliberately not a field. -/
structure PositiveDegreeSelfDualCompletion where
  completed : ℂ → ℂ
  differentiable : Differentiable ℂ completed
  growthConstant : ℝ
  growthExponent : ℝ
  growthConstant_nonneg : 0 ≤ growthConstant
  growthExponent_nonneg : 0 ≤ growthExponent
  growthExponent_lt_two : growthExponent < 2
  growth : ∀ z,
    ‖completed z‖ ≤
      Real.exp (growthConstant * (1 + ‖z‖) ^ growthExponent)
  superlinearRay : ∀ A : ℝ, ∃ sigma : ℝ, 1 ≤ sigma ∧
    A * sigma < Real.log ‖completed (sigma : ℂ)‖
  zero_mem_openUnitStrip : ∀ {z : ℂ}, completed z = 0 → 0 < z.re ∧ z.re < 1
  zero_reflect : ∀ {z : ℂ}, completed z = 0 → completed (1 - z) = 0

namespace PositiveDegreeSelfDualCompletion

variable (F : PositiveDegreeSelfDualCompletion)

/-- Superlinear ray growth supplies an explicit nonzero value, so isolated-zero theory applies. -/
theorem exists_completed_ne_zero : ∃ z, F.completed z ≠ 0 := by
  obtain ⟨sigma, _, hsigma⟩ := F.superlinearRay 0
  refine ⟨(sigma : ℂ), ?_⟩
  intro hzero
  rw [hzero, norm_zero, Real.log_zero, zero_mul] at hsigma
  exact lt_irrefl 0 hsigma

/-- Positive-degree analytic growth forces infinitely many distinct completed zeros. -/
theorem zeroSet_infinite : {z : ℂ | F.completed z = 0}.Infinite := by
  exact _root_.RHTower.zeroSet_infinite_of_subquadratic_superlinear_ray
    F.differentiable F.growthExponent_nonneg F.growthExponent_lt_two
    F.growthConstant_nonneg F.growth F.superlinearRay

/-- Zeros are finite in every closed disc, derived from entire nontriviality. -/
theorem zeros_closedBall_finite (c : ℂ) (R : ℝ) :
    {z ∈ Metric.closedBall c R | F.completed z = 0}.Finite := by
  obtain ⟨w, hw⟩ := F.exists_completed_ne_zero
  have hA : AnalyticOnNhd ℂ F.completed Set.univ :=
    F.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hcod :
      (F.completed ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    hA.preimage_zero_mem_codiscreteWithin
      (x := w) hw (Set.mem_univ _) isConnected_univ
  have hcodK :
      (F.completed ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Metric.closedBall c R) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine ((isCompact_closedBall c R).finite_sdiff_of_mem_codiscreteWithin hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

/-- Dependency-closed complete-strip divisor derived from the automorphic analytic interface. -/
def toCompleteStripReflectionDivisor : CompleteStripReflectionDivisor where
  completed := F.completed
  zeroSetInfinite := F.zeroSet_infinite
  zero_mem_openUnitStrip := F.zero_mem_openUnitStrip
  zero_reflect := F.zero_reflect
  zeros_closedBall_finite := F.zeros_closedBall_finite

/-- **P3 for every positive-degree self-dual analytic completion.**  Its Real-corona idempotent
does not lie in the natural dense endpoint-entire reflection crossed product. -/
theorem corona_not_mem_smoothCrossedProductRange :
    let D := F.toCompleteStripReflectionDivisor
    let R := D.holomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((D.upperSector ∪ D.lowerSector : Set ℂ) → ℂ)) := R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent D.upperSector D.lowerSector) ∉
      Set.range (InvariantSubalgebra.crossedProductInclusion
        (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) :=
  F.toCompleteStripReflectionDivisor.corona_not_mem_smoothCrossedProductRange

end PositiveDegreeSelfDualCompletion
end GaloisForLFunctions.RHTower

import GaloisForLFunctions.HTGeometry.KernelControlSurjectivityCriterion
import GaloisForLFunctions.HTGeometry.LinftyKernelControlContinuity

/-!
# Kernel control maps on indicators

The surjectivity criterion tests a control map on indicators of measurable sets.  For a control map
given by pairing against an `L¹` kernel this test evaluates to a set integral of the kernel, and in
a finite tuple of coordinates it evaluates coordinatewise.

With that representation the criterion applies to every such control map, leaving only rigidity of
the kernel to be checked.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Pairing an `L¹` kernel against the indicator of a measurable set is the set integral. -/
theorem linftyLpPairingRight_indicatorLpTopGen
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure α) (K : Lp V 1 μ) {S : Set α} (hS : MeasurableSet S) :
    linftyLpPairingRight μ K (indicatorLpTopGen μ hS) = ∫ x in S, K x ∂μ := by
  rw [linftyLpPairingRight_apply, ← integral_indicator hS]
  refine integral_congr_ae ?_
  filter_upwards [indicatorLpTopGen_coeFn μ hS] with x hx
  rw [hx]
  by_cases h : x ∈ S
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The kernel control map on an indicator, read in one coordinate of a finite tuple. -/
theorem linftyLpKernelControl_indicatorLpTopGen_apply
    {σ : Type*} [Fintype σ]
    (μ : Measure α) (K : Lp (σ → ℂ) 1 μ) {S : Set α} (hS : MeasurableSet S) (s : σ) :
    linftyLpKernelControl μ K (indicatorLpTopGen μ hS) s = ∫ x in S, K x s ∂μ := by
  have hint : Integrable (fun x => (K : α → (σ → ℂ)) x) μ := L1.integrable_coeFn K
  rw [linftyLpKernelControl_apply, linftyLpPairingRight_indicatorLpTopGen μ K hS]
  exact ((ContinuousLinearMap.proj s : (σ → ℂ) →L[ℝ] ℂ).integral_comp_comm hint.restrict).symm

/-- **Surjectivity of a kernel control map from kernel rigidity.**  A bounded-density control map
given by pairing against an `L¹` kernel is surjective as soon as no nonzero coefficient packet makes
the paired kernel have vanishing real part almost everywhere.

All the measure theory is discharged; rigidity of the kernel is the only remaining input. -/
theorem surjective_linftyLpKernelControl_of_rigidity
    {σ : Type*} [Fintype σ]
    (μ : Measure α) (K : Lp (σ → ℂ) 1 μ)
    (hrig : ∀ c : σ → ℂ,
      (∀ᵐ x ∂μ, (∑ s : σ, c s * K x s).re = 0) → ∀ s, c s = 0) :
    Function.Surjective (linftyLpKernelControl μ K) := by
  have hint : Integrable (fun x => (K : α → (σ → ℂ)) x) μ := L1.integrable_coeFn K
  refine surjective_of_kernel_ae_re_rigidity μ
    (linftyLpKernelControl μ K).toLinearMap (fun x s => K x s) ?_ ?_ hrig
  · intro s
    exact (ContinuousLinearMap.proj s : (σ → ℂ) →L[ℝ] ℂ).integrable_comp hint
  · intro S hS s
    exact linftyLpKernelControl_indicatorLpTopGen_apply μ K hS s

end

end GaloisForLFunctions.HTGeometry

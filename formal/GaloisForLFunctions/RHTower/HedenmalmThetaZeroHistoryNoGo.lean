import GaloisForLFunctions.RHTower.HedenmalmThetaMetricCommutator
import GaloisForLFunctions.RHTower.HedenmalmClosedWeightedDerivative

/-!
# No bounded injective symmetrizer of the full theta compact inverse

The full compact source inverse has a nonzero constant kernel vector and dense range.
Its adjoint is therefore injective. Any bounded operator intertwining the inverse with
its adjoint must kill the constant vector, even without a positivity hypothesis.

This theorem concerns the full source inverse. The centered quotient requires a separate
source derivative vector to exhibit its nonzero kernel; that stronger result is not asserted here.
-/

open Complex MeasureTheory

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmClosedWeightedDerivative

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

private theorem thetaKernelOperator_pinnedOne_local :
    thetaKernelOperator pinnedOne = 0 := by
  have hGinj : Function.Injective thetaMetricOperator :=
    metricOperator_injective thetaSource thetaMetricBound_nonneg
      norm_metricSymbol_thetaSource_le
  apply hGinj
  have h := congrArg (fun T : ThetaH →L[ℂ] ThetaH => T pinnedOne)
    thetaMetricOperator_mul_thetaKernelOperator
  simpa only [ContinuousLinearMap.mul_apply, pinnedVolterraCLM_pinnedOne,
    map_zero, ContinuousLinearMap.smul_apply, smul_zero] using h

/-- Dense range follows from the already proved dense range of the centered restriction. -/
theorem thetaKernelOperator_dense_range :
    Dense (thetaKernelOperator.range : Set ThetaH) := by
  apply thetaCenteredSourceInverse_dense_range.mono
  intro y hy
  rcases hy with ⟨x, rfl⟩
  refine ⟨(x : ThetaH), ?_⟩
  change thetaKernelOperator (x : ThetaH) =
    thetaCompactSourceInverse (x : ThetaH)
  rfl

/-- The full compact source inverse has injective adjoint. -/
theorem thetaKernelOperator_adjoint_injective :
    Function.Injective thetaKernelOperator.adjoint := by
  intro x y hxy
  apply thetaKernelOperator_dense_range.eq_of_inner_left ℂ
  intro _ hk
  rcases hk with ⟨k, rfl⟩
  calc
    inner ℂ x (thetaKernelOperator k) =
        inner ℂ (thetaKernelOperator.adjoint x) k :=
      (thetaKernelOperator.adjoint_inner_left k x).symm
    _ = inner ℂ (thetaKernelOperator.adjoint y) k :=
      congrArg (fun z => inner ℂ z k) hxy
    _ = inner ℂ y (thetaKernelOperator k) :=
      thetaKernelOperator.adjoint_inner_left k y

/-- No bounded injective operator can intertwine the full theta inverse with its adjoint. -/
theorem thetaKernelOperator_no_injective_bounded_symmetrizer :
    ¬ ∃ G : ThetaH →L[ℂ] ThetaH,
      Function.Injective G ∧
        G.comp thetaKernelOperator = thetaKernelOperator.adjoint.comp G := by
  rintro ⟨G, hGinj, hsym⟩
  have h := congrArg (fun T : ThetaH →L[ℂ] ThetaH => T pinnedOne) hsym
  have hzero : thetaKernelOperator.adjoint (G pinnedOne) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply,
      thetaKernelOperator_pinnedOne_local, map_zero] using h.symm
  have hGone : G pinnedOne = 0 :=
    thetaKernelOperator_adjoint_injective (by simpa using hzero)
  exact pinnedOne_ne_zero (hGinj (by simpa using hGone))

end

end RHTower.HedenmalmThetaSource

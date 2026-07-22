import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier

/-!
# All-strict-half-power Möbius--Laplace criterion

Mellin analyticity on `Re s > 1/2` does not require one uniform critical bound.  It is enough that
the concrete Möbius--Laplace transform satisfy `O(x^(-b))` separately for every `b > 1/2`, with a
constant depending on `b`.  This is the analytic consumer for a one-sided
`N^(1+o(1))` additive-triangle source estimate.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- Subpower closure of the critical decay target: every strict exponent above `1/2` is
available, without a uniform constant or a fixed logarithmic loss. -/
def MobiusDiscreteLaplaceAllStrictHalfPowerDecay : Prop :=
  ∀ b : ℝ, 1 / 2 < b →
    mobiusDiscreteLaplaceTransform =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b))

/-- All strict half-power estimates make the concrete Mellin transform analytic throughout the
open right half-plane.  The exponent is chosen separately at each Mellin point. -/
theorem analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_allStrictHalfPower
    (hdecay : MobiusDiscreteLaplaceAllStrictHalfPowerDecay) :
    AnalyticOnNhd ℂ (mellin mobiusDiscreteLaplaceTransform) rightHalf := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_rightHalf
  let b : ℝ := (1 / 2 + s.re) / 2
  have hhalf : 1 / 2 < b := by
    dsimp [b]
    linarith [mem_rightHalf.mp hs]
  have hbs : b < s.re := by
    dsimp [b]
    linarith [mem_rightHalf.mp hs]
  exact (mellin_differentiableAt_of_isBigO_rpow_exp
    (a := 1) (b := b) (by norm_num)
    mobiusDiscreteLaplaceTransform_locallyIntegrableOn
    mobiusDiscreteLaplaceTransform_isBigO_exp_neg
    (hdecay b hhalf) hbs).differentiableWithinAt

/-- Every-strict-half-power decay discharges the denominator-free Mellin continuation wall. -/
theorem mobiusLaplaceMellinContinuationWall_of_allStrictHalfPower
    (hdecay : MobiusDiscreteLaplaceAllStrictHalfPowerDecay) :
    MobiusLaplaceMellinContinuationWall :=
  mobiusLaplaceMellinContinuationWall_of_analyticOnNhd_mellin
    (analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_allStrictHalfPower hdecay)

/-- **Subpower Möbius--Laplace criterion for RH.**  Constants may depend arbitrarily on the strict
power exponent; no fixed critical logarithmic loss or uniform zero-multiplicity bound is needed. -/
theorem mobiusDiscreteLaplaceAllStrictHalfPowerDecay_implies_riemannHypothesis
    (hdecay : MobiusDiscreteLaplaceAllStrictHalfPowerDecay) :
    RiemannHypothesis :=
  mobiusLaplaceMellinContinuationWall_implies_riemannHypothesis
    (mobiusLaplaceMellinContinuationWall_of_allStrictHalfPower hdecay)

end

end RHTower

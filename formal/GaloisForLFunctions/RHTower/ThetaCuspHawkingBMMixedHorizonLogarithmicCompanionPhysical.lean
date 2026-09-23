import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonLogarithmicCompanionAnalytic
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTotalRenormalizedAngularPeriod

/-!
# Physical BM resonant logarithmic companion

The Xi momentum strip puts both shifted mixed-horizon Gauss parameters in the positive chamber.
Consequently the convergent resonant companion applies to every Xi fibre. This module specializes
the analytic Gauss ODE and identifies its exact deck jump with the previously normalized physical
BM monodromy coefficient times the regular radial mode.
-/

open Complex Nat Polynomial

namespace RHTower

noncomputable section

/-- First shifted mixed-horizon parameter has positive real part on every Xi fibre. -/
theorem d4BMXiMixedHorizonResonantShiftedA_re_pos
    (n k : ℕ) (q : XiZeroCopy) :
    0 < (d4HypergeometricResonantShiftedA
      (d4BMMixedHorizonFrobeniusOrder n k)
      (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))).re := by
  rw [d4HypergeometricResonantShiftedA, d4BMMixedHorizonComplexA,
    d4BMCausalHypergeometricA_plusMinus]
  have him := (d4BMXiMixedHorizonAngularMomentum_im_mem_openHalf q).2
  simp [d4BMMixedHorizonFrobeniusOrder]
  linarith

/-- Second shifted mixed-horizon parameter has positive real part on every Xi fibre. -/
theorem d4BMXiMixedHorizonResonantShiftedB_re_pos
    (n k : ℕ) (q : XiZeroCopy) :
    0 < (d4HypergeometricResonantShiftedA
      (d4BMMixedHorizonFrobeniusOrder n k)
      (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))).re := by
  rw [d4HypergeometricResonantShiftedA, d4BMMixedHorizonComplexB,
    d4BMCausalHypergeometricB_plusMinus]
  have him := (d4BMXiMixedHorizonAngularMomentum_im_mem_openHalf q).1
  simp [d4BMMixedHorizonFrobeniusOrder]
  linarith

def d4BMXiMixedHorizonLogarithmicCompanionValue
    (n k : ℕ) (q : XiZeroCopy) : ℂ → ℂ :=
  d4HypergeometricResonantLogarithmicCompanionValue
    (d4BMMixedHorizonFrobeniusOrder n k)
    (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
    (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))

def d4BMXiMixedHorizonLogarithmicCompanionFirstDerivative
    (n k : ℕ) (q : XiZeroCopy) : ℂ → ℂ :=
  d4HypergeometricResonantLogarithmicCompanionFirstDerivative
    (d4BMMixedHorizonFrobeniusOrder n k)
    (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
    (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))

def d4BMXiMixedHorizonLogarithmicCompanionSecondDerivative
    (n k : ℕ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  d4HypergeometricResonantLogarithmicCompanionSecondDerivative
    (d4BMMixedHorizonFrobeniusOrder n k)
    (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
    (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)) z

/-- The new coefficientwise analytic regular branch is the existing exact BM regular radial
solution, not a second normalization. -/
theorem d4BMXiMixedHorizonResonantRegularBranchValue_eq
    (n k : ℕ) (q : XiZeroCopy) (z : ℂ) (hz : ‖z‖ₑ < 1) :
    d4HypergeometricResonantRegularBranchValue
          (d4BMMixedHorizonFrobeniusOrder n k)
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)) z =
      d4BMMixedHorizonRegularBranch n k (d4BMXiMixedHorizonAngularMomentum q) z := by
  rw [d4HypergeometricResonantRegularBranchValue_eq_pow_mul_factor
    (d4BMMixedHorizonFrobeniusOrder n k)
    (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
    (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)) z
    (d4BMXiMixedHorizonResonantShiftedA_re_pos n k q)
    (d4BMXiMixedHorizonResonantShiftedB_re_pos n k q) hz]
  rfl

/-- Every Xi fibre carries the actual mixed-horizon logarithmic Gauss solution on the principal
slit unit disk. -/
theorem d4BMXiMixedHorizonLogarithmicCompanion_analyticEulerODE
    (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (hzslit : z ∈ Complex.slitPlane) :
    z ^ (2 : ℕ) * (1 - z) *
          d4BMXiMixedHorizonLogarithmicCompanionSecondDerivative n k q z +
        (-(d4BMMixedHorizonFrobeniusOrder n k : ℂ) * z -
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q) +
            d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q) + 1) * z ^ (2 : ℕ)) *
          d4BMXiMixedHorizonLogarithmicCompanionFirstDerivative n k q z -
      d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q) *
        d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q) * z *
          d4BMXiMixedHorizonLogarithmicCompanionValue n k q z = 0 := by
  exact d4HypergeometricResonantLogarithmicCompanion_analyticEulerODE
    (d4BMMixedHorizonFrobeniusOrder n k)
    (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
    (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)) z
    (d4BMXiMixedHorizonResonantShiftedA_re_pos n k q)
    (d4BMXiMixedHorizonResonantShiftedB_re_pos n k q) hz hzslit

/-- Physical deck jump equals the normalized BM monodromy coefficient times the actual regular
resonant radial mode. -/
theorem d4BMXiMixedHorizonLogarithmicCompanionOnSheet_sub
    (n k : ℕ) (q : XiZeroCopy) (z logPlus logMinus : ℂ)
    (hlog : logPlus - logMinus = 2 * Real.pi * Complex.I) :
    d4HypergeometricResonantLogarithmicCompanionOnSheet
          (d4BMMixedHorizonFrobeniusOrder n k)
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
          z logPlus -
        d4HypergeometricResonantLogarithmicCompanionOnSheet
          (d4BMMixedHorizonFrobeniusOrder n k)
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
          z logMinus =
      d4BMMixedHorizonComplexMonodromyJump n k
          (d4BMXiMixedHorizonAngularMomentum q) *
        d4HypergeometricResonantRegularBranchValue
          (d4BMMixedHorizonFrobeniusOrder n k)
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)) z := by
  have h := d4HypergeometricResonantLogarithmicCompanionOnSheet_sub
    (d4BMMixedHorizonFrobeniusOrder n k)
    (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
    (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
    z logPlus logMinus hlog
  simpa [d4BMMixedHorizonComplexMonodromyJump, mul_assoc] using h

/-- Exact sheet discontinuity is the previously defined Xi-fibre monodromy mode pointwise. -/
theorem d4BMXiMixedHorizonLogarithmicCompanionOnSheet_sub_eq_exactMonodromyMode
    (n k : ℕ) (q : XiZeroCopy) (z logPlus logMinus : ℂ)
    (hz : ‖z‖ₑ < 1)
    (hlog : logPlus - logMinus = 2 * Real.pi * Complex.I) :
    d4HypergeometricResonantLogarithmicCompanionOnSheet
          (d4BMMixedHorizonFrobeniusOrder n k)
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
          z logPlus -
        d4HypergeometricResonantLogarithmicCompanionOnSheet
          (d4BMMixedHorizonFrobeniusOrder n k)
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
          z logMinus =
      d4BMXiMixedHorizonExactMonodromyMode n k q z := by
  rw [d4BMXiMixedHorizonLogarithmicCompanionOnSheet_sub n k q z
    logPlus logMinus hlog,
    d4BMXiMixedHorizonResonantRegularBranchValue_eq n k q z hz]
  rfl

/-- Explicit radial response to one scalar projected source amplitude on a chosen logarithm sheet. -/
def d4BMXiMixedHorizonLogarithmicCompanionSheetResponse
    (n k : ℕ) (q : XiZeroCopy) (logSheet : ℂ → ℂ) : ℂ →ₗ[ℂ] (ℂ → ℂ) where
  toFun amplitude z := amplitude *
    d4HypergeometricResonantLogarithmicCompanionOnSheet
      (d4BMMixedHorizonFrobeniusOrder n k)
      (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
      (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
      z (logSheet z)
  map_add' x y := by
    funext z
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext z
    simp
    ring

/-- Deck difference of explicit sheet responses is rank one: projected amplitude times the exact
Xi-fibre monodromy mode. -/
theorem d4BMXiMixedHorizonLogarithmicCompanionSheetResponse_sub_apply
    (n k : ℕ) (q : XiZeroCopy) (logPlus logMinus : ℂ → ℂ)
    (amplitude z : ℂ) (hz : ‖z‖ₑ < 1)
    (hlog : logPlus z - logMinus z = 2 * Real.pi * Complex.I) :
    ((d4BMXiMixedHorizonLogarithmicCompanionSheetResponse n k q logPlus -
        d4BMXiMixedHorizonLogarithmicCompanionSheetResponse n k q logMinus) amplitude) z =
      amplitude * d4BMXiMixedHorizonExactMonodromyMode n k q z := by
  rw [LinearMap.sub_apply]
  change amplitude *
        d4HypergeometricResonantLogarithmicCompanionOnSheet
          (d4BMMixedHorizonFrobeniusOrder n k)
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
          z (logPlus z) -
      amplitude *
        d4HypergeometricResonantLogarithmicCompanionOnSheet
          (d4BMMixedHorizonFrobeniusOrder n k)
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
          z (logMinus z) = _
  rw [← mul_sub]
  rw [d4BMXiMixedHorizonLogarithmicCompanionOnSheet_sub_eq_exactMonodromyMode
    n k q z (logPlus z) (logMinus z) hz hlog]

/-- Sheet response after an explicit linear projection of a nonlinear radial source onto its
resonant scalar amplitude. -/
def d4BMXiMixedHorizonProjectedLogarithmicCompanionSheetResponse
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (n k : ℕ) (q : XiZeroCopy) (projection : Y →ₗ[ℂ] ℂ)
    (logSheet : ℂ → ℂ) : Y →ₗ[ℂ] (ℂ → ℂ) :=
  (d4BMXiMixedHorizonLogarithmicCompanionSheetResponse n k q logSheet).comp projection

/-- All source dependence in deck discontinuity is the single explicit projection amplitude. -/
theorem d4BMXiMixedHorizonProjectedLogarithmicCompanionSheetResponse_sub_apply
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (n k : ℕ) (q : XiZeroCopy) (projection : Y →ₗ[ℂ] ℂ)
    (logPlus logMinus : ℂ → ℂ) (source : Y) (z : ℂ) (hz : ‖z‖ₑ < 1)
    (hlog : logPlus z - logMinus z = 2 * Real.pi * Complex.I) :
    ((d4BMXiMixedHorizonProjectedLogarithmicCompanionSheetResponse
          n k q projection logPlus -
        d4BMXiMixedHorizonProjectedLogarithmicCompanionSheetResponse
          n k q projection logMinus) source) z =
      projection source * d4BMXiMixedHorizonExactMonodromyMode n k q z := by
  exact d4BMXiMixedHorizonLogarithmicCompanionSheetResponse_sub_apply
    n k q logPlus logMinus (projection source) z hz hlog

end

end RHTower

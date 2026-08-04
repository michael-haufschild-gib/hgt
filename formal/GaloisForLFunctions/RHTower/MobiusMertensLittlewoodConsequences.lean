import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.RHTower.MobiusMertensFourthConvolutionCriterion
import GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionOrderLaw
import GaloisForLFunctions.RHTower.MobiusMertensReversalEnergyCriterion
import GaloisForLFunctions.RHTower.MobiusEnergyAnalyticUnitWallUniversalityLaw

/-!
# Unconditional consequences of the closed Mertens criterion

The RH-to-Mertens theorem removes the common `hLittlewood` premise from the additive-energy,
even-convolution, reversal-energy, Mellin-energy, and analytic-unit-wall criteria.
-/

open Complex Set

namespace RHTower

noncomputable section

theorem mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_iff_riemannHypothesis :
    MobiusAdditiveTriangleSecondCesaroSubpowerUpperBound ↔ RiemannHypothesis :=
  mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_iff_riemannHypothesis_of_mertens
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound

theorem mobiusMertensFourthConvolutionSubpowerUpperBound_iff_riemannHypothesis :
    MobiusMertensFourthConvolutionSubpowerUpperBound ↔ RiemannHypothesis :=
  mobiusMertensFourthConvolutionSubpowerUpperBound_iff_riemannHypothesis_of_mertens
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound

theorem mobiusMertensEvenConvolutionSubpowerUpperBound_iff_riemannHypothesis
    {k : ℕ} (hk : 0 < k) :
    MobiusMertensEvenConvolutionSubpowerUpperBound k ↔ RiemannHypothesis :=
  mobiusMertensEvenConvolutionSubpowerUpperBound_iff_riemannHypothesis_of_mertens hk
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound

theorem mobiusMertensPalindromicEnergySubpowerUpperBound_iff_riemannHypothesis :
    MobiusMertensPalindromicEnergySubpowerUpperBound ↔ RiemannHypothesis :=
  mobiusMertensPalindromicEnergySubpowerUpperBound_iff_riemannHypothesis_of_mertens
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound

theorem mobiusDiscreteLaplaceAllStrictHalfPowerDecay_iff_riemannHypothesis :
    MobiusDiscreteLaplaceAllStrictHalfPowerDecay ↔ RiemannHypothesis := by
  constructor
  · exact mobiusDiscreteLaplaceAllStrictHalfPowerDecay_implies_riemannHypothesis
  · intro hRH
    exact mobiusMertensAllStrictHalfPowerBound_implies_allStrictHalfPowerDecay
      (riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound hRH)

theorem mobiusLaplaceStrictRightEnergyFinite_iff_riemannHypothesis :
    MobiusLaplaceStrictRightEnergyFinite ↔ RiemannHypothesis :=
  mobiusLaplaceStrictRightEnergyFinite_iff_riemannHypothesis_of_mertens
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound

theorem mobiusLaplaceCofinalStrictRightEnergyFinite_iff_riemannHypothesis :
    MobiusLaplaceCofinalStrictRightEnergyFinite ↔ RiemannHypothesis :=
  mobiusLaplaceCofinalStrictRightEnergyFinite_iff_riemannHypothesis_of_mertens
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound

/-- Every analytic unit on the RH half-plane produces the same unconditional wall criterion as
strict-right Möbius logarithmic energy. -/
theorem mobiusLaplaceStrictRightEnergyFinite_iff_unitTwistedWall
    {U : ℂ → ℂ} (hU : AnalyticOnNhd ℂ U rightHalf)
    (hUne : ∀ s ∈ rightHalf, U s ≠ 0) :
    MobiusLaplaceStrictRightEnergyFinite ↔
      MobiusLaplaceUnitTwistedMellinContinuationWall U :=
  mobiusLaplaceStrictRightEnergyFinite_iff_unitTwistedWall_of_mertens hU hUne
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound

theorem mobiusLaplaceStrictRightEnergyFinite_iff_liouvilleSquareDilationWall :
    MobiusLaplaceStrictRightEnergyFinite ↔
      MobiusLiouvilleSquareDilationMellinContinuationWall :=
  mobiusLaplaceStrictRightEnergyFinite_iff_liouvilleSquareDilationWall_of_mertens
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound

end

end RHTower

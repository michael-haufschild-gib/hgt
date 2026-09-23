import GaloisForLFunctions.HTGeometry.HorizonLogThirdJetCore
import GaloisForLFunctions.HTGeometry.LiteralSourceHorizonPowerJets
import GaloisForLFunctions.HTGeometry.HorizonPowerThirdDerivativeRule

/-! Third derivative of the literal complex source horizon power. -/

namespace GaloisForLFunctions.HTGeometry
open Complex
noncomputable section
set_option autoImplicit false

def horizonPowerThirdCore (α : ℂ) (z : ℝ) : ℂ :=
  ((horizonLogThirdCore z : ℂ) * α +
    3 * ((literalSourceHorizonLogSecond z : ℂ) * α) *
      ((literalSourceHorizonLogFirst z : ℂ) * α) +
    ((literalSourceHorizonLogFirst z : ℂ) * α) ^ (3 : ℕ)) * literalSourceHorizonPower α z

theorem literalSourceHorizonPowerSecond_hasDerivAt (α : ℂ) (z : ℝ) (hz : z < 1) :
    HasDerivAt (literalSourceHorizonPowerSecond α) (horizonPowerThirdCore α z) z := by
  have hL := literalSourceHorizonLog_derivatives hz
  have hL1 : HasDerivAt (fun x : ℝ => (literalSourceHorizonLogFirst x : ℂ))
      (literalSourceHorizonLogSecond z : ℂ) z := hL.2.ofReal_comp
  have hL2 : HasDerivAt (fun x : ℝ => (literalSourceHorizonLogSecond x : ℂ))
      (horizonLogThirdCore z : ℂ) z := (literalSourceHorizonLogSecond_hasDerivAt z hz).ofReal_comp
  have hP := literalSourceHorizonPower_derivatives α hz
  have hg1 := hL1.mul_const α
  have hg2 := hL2.mul_const α
  have hfirst : literalSourceHorizonPowerFirst α = fun x : ℝ =>
      ((literalSourceHorizonLogFirst x : ℂ) * α) * literalSourceHorizonPower α x := by
    funext x
    rfl
  have hsecond : literalSourceHorizonPowerSecond α = fun x : ℝ =>
      ((literalSourceHorizonLogSecond x : ℂ) * α +
        ((literalSourceHorizonLogFirst x : ℂ) * α) ^ (2 : ℕ)) * literalSourceHorizonPower α x := by
    funext x
    rfl
  simpa only [horizonPowerThirdCore] using third_deriv_of_quadratic_log_jet
    (P := literalSourceHorizonPower α)
    (P₁ := literalSourceHorizonPowerFirst α)
    (P₂ := literalSourceHorizonPowerSecond α)
    (X := fun x : ℝ => (literalSourceHorizonLogFirst x : ℂ) * α)
    (Y := fun x : ℝ => (literalSourceHorizonLogSecond x : ℂ) * α)
    (Z := fun x : ℝ => (horizonLogThirdCore x : ℂ) * α)
    hg1 hg2 hP.1 hfirst hsecond

end
end GaloisForLFunctions.HTGeometry

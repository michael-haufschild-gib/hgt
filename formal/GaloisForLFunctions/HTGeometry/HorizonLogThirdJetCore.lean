import GaloisForLFunctions.HTGeometry.HorizonLogHeightThirdJetCore

/-! Third derivative of the literal source logarithmic height. -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

def horizonLogThirdCore (z : ℝ) : ℝ :=
  horizonLogHeightThirdCore z / literalSourceHorizonHeight z -
    3 * literalSourceHorizonHeightSecond z * literalSourceHorizonHeightFirst z /
      literalSourceHorizonHeight z ^ 2 +
    2 * literalSourceHorizonHeightFirst z ^ 3 / literalSourceHorizonHeight z ^ 3

theorem literalSourceHorizonLogSecond_hasDerivAt (z : ℝ) (hz : z < 1) :
    HasDerivAt literalSourceHorizonLogSecond (horizonLogThirdCore z) z := by
  have hh : literalSourceHorizonHeight z ≠ 0 := by
    dsimp [literalSourceHorizonHeight]
    positivity
  have hd := literalSourceHorizonHeight_derivatives hz
  have hd3 := literalSourceHorizonHeightSecond_hasDerivAt z hz
  have hn := (hd3.mul hd.1).sub (hd.2.mul hd.2)
  have hden := hd.1.pow 2
  have hquot := hn.div hden (pow_ne_zero 2 hh)
  change HasDerivAt
    (fun x : ℝ => (literalSourceHorizonHeightSecond x * literalSourceHorizonHeight x -
      literalSourceHorizonHeightFirst x * literalSourceHorizonHeightFirst x) /
        literalSourceHorizonHeight x ^ 2) (horizonLogThirdCore z) z
  apply hquot.congr_deriv
  dsimp [horizonLogThirdCore]
  field_simp [hh]
  ring

end
end GaloisForLFunctions.HTGeometry

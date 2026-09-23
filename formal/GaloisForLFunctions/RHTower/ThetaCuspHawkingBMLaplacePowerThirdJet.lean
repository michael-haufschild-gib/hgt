import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplacePowerJets

/-!
The literal third radial jet of the positive complex power.

The source-pole strip requires a cubic endpoint subtraction.  This is the exact
third jet of the source's existing positive-radius power, with no asymptotic
replacement.
-/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The literal third positive-radius derivative of the original complex power. -/
def powerThird (a : ℂ) (z : ℝ) : ℂ :=
  a * (a - 1) * (a - 2) * power a z / (z : ℂ) ^ (3 : ℕ)

/-- The third radial jet follows by differentiating the already literal second jet. -/
theorem powerSecond_hasDerivAt (a : ℂ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (powerSecond a) (powerThird a z) z := by
  have hz0 : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hfirst := (power_derivatives a hz).1
  have hnum := hfirst.const_mul (a * (a - 1))
  have hquot := hnum.div (((hasDerivAt_id z).ofReal_comp).pow 2) (pow_ne_zero 2 hz0)
  apply hquot.congr_deriv
  dsimp [powerSecond, powerThird, powerFirst]
  field_simp [hz0]

/-- All three literal positive-radius derivatives of the original power. -/
theorem power_derivatives_three (a : ℂ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (power a) (powerFirst a z) z ∧
      HasDerivAt (powerFirst a) (powerSecond a z) z ∧
      HasDerivAt (powerSecond a) (powerThird a z) z :=
  ⟨(power_derivatives a hz).1, (power_derivatives a hz).2,
    powerSecond_hasDerivAt a hz⟩

end
end RHTower.D4BMLaplaceRadial

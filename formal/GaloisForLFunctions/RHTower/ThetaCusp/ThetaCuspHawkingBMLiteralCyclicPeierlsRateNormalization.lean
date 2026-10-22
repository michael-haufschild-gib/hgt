import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularMasterCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspIndicialSelection

/-!
# Literal cyclic Peierls rate normalization

The cusp Peierls clock and the radial mixed-current rate are two normalizations
of one literal source carrier.  This leaf proves their exact factor-two bridge,
so a clock obstruction stated for the cusp source can be transported to the
radial residual without conflating identically named definitions.

Proof-chain role:
`cusp Peierls clock = 2 * radial source rate`
`-> exact clock handoff to literal radial residual`
`-> cyclic cap/square leading-coefficient noncancellation`
`-> RBH/PW B2 carrier extinction`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsRateNormalization

noncomputable section
set_option autoImplicit false

/-- The literal cusp Peierls clock is twice the physical radial source rate. -/
theorem cusp_rate_eq_twice_radial_rate (q : XiZeroCopy) (branch : Bool) :
    D4BMCuspProjection.physicalRate q branch =
      2 * D4BMModularCore.physicalRate q branch := by
  cases branch <;> rfl

/-- The two radial source arms carry complementary half-clocks of total `-3`. -/
theorem complementary_radial_rate_sum (q : XiZeroCopy) :
    D4BMModularCore.physicalRate q true + D4BMModularCore.physicalRate q false =
      (-3 : ℂ) := by
  simp only [D4BMModularCore.physicalRate, if_true, Bool.false_eq_true, if_false]
  ring

/-- The cusp complementary clock is precisely twice the radial complementary clock. -/
theorem complementary_cusp_rate_eq_twice_radial_sum (q : XiZeroCopy) :
    D4BMCuspProjection.physicalRate q true + D4BMCuspProjection.physicalRate q false =
      2 * (D4BMModularCore.physicalRate q true + D4BMModularCore.physicalRate q false) := by
  rw [cusp_rate_eq_twice_radial_rate, cusp_rate_eq_twice_radial_rate]
  ring

end
end RHTower.D4BMLiteralCyclicPeierlsRateNormalization

import GaloisForLFunctions.RHTower.CHMDKleinGordonEnergyPositivityAndOriginMaximum
import GaloisForLFunctions.RHTower.CHMDQuarticMomentAndSecondOrderPacketPositivity
import GaloisForLFunctions.RHTower.CHMDSmallScalePacketPositivityFirstOrder
import GaloisForLFunctions.SquareRootThreshold.TheSideIsTheDepthAndTheWidthIsItsSupremum

/-!
# Strict positivity of the zero-measure moments of `ζ`

The Klein–Gordon energy moment, the quartic moment and the wave at the origin were proved strictly
positive for a nonempty zero configuration.  `zetaZeroConfig_carrier_nonempty` (a zero of `ζ` in
the open critical strip) supplies the nonemptiness.
-/

noncomputable section

namespace RHTower

/-- The zero configuration of `ζ`, as a nonempty type. -/
theorem nonempty_zetaZeroConfig_carrier : Nonempty Zeta23.zetaZeroConfig.carrier :=
  GaloisForLFunctions.SquareRootThreshold.zetaZeroConfig_carrier_nonempty.to_subtype

/-- The Klein–Gordon energy moment of the zeros of `ζ` is strictly positive. -/
theorem CHMDEnergyPositivity.kgEnergyMoment_pos_unconditional :
    0 < CHMDEnergyPositivity.kgEnergyMoment :=
  haveI := nonempty_zetaZeroConfig_carrier
  CHMDEnergyPositivity.kgEnergyMoment_pos

/-- The quartic Klein–Gordon moment of the zeros of `ζ` is strictly positive. -/
theorem CHMDQuarticMoment.kgQuarticMoment_pos_unconditional :
    0 < CHMDQuarticMoment.kgQuarticMoment :=
  haveI := nonempty_zetaZeroConfig_carrier
  CHMDQuarticMoment.kgQuarticMoment_pos

/-- The CHMD wave of the zeros of `ζ` is strictly positive at the origin. -/
theorem CHMDSmallScale.chmdWave_zero_pos_unconditional : 0 < CHMDGrowthCollapse.chmdWave 0 :=
  haveI := nonempty_zetaZeroConfig_carrier
  CHMDSmallScale.chmdWave_zero_pos

end RHTower

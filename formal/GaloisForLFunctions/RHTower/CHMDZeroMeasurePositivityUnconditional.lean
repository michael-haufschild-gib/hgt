import GaloisForLFunctions.RHTower.CHMDKleinGordonEnergyPositivityAndOriginMaximum
import GaloisForLFunctions.RHTower.CHMDQuarticMomentAndSecondOrderPacketPositivity
import GaloisForLFunctions.RHTower.CHMDSmallScalePacketPositivityFirstOrder
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite

/-!
# Strict positivity of the zero-measure moments of `ζ`

The Klein–Gordon energy moment, the quartic moment and the wave at the origin were proved strictly
positive for a nonempty zero configuration.  `exists_riemannZeta_zero_mem_openStrip` (a zero of `ζ`
in the open critical strip) supplies the nonemptiness.
-/

noncomputable section

namespace RHTower

/-- The zero configuration of `ζ`, as a nonempty type. -/
theorem nonempty_zetaZeroConfig_carrier : Nonempty Zeta23.zetaZeroConfig.carrier := by
  obtain ⟨ρ, h0, h1, hzero⟩ := exists_riemannZeta_zero_mem_openStrip
  exact ⟨⟨ρ, show Zeta23.IsNontrivialZero ρ from ⟨hzero, h0, h1⟩⟩⟩

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

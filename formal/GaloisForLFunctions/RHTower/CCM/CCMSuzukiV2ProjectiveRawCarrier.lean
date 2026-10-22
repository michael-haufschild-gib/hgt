import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaCovarianceReflection
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2LivsicCharacteristic
import GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectiveDefectBoundary

/-!
# Raw completed-source carrier for Suzuki v2

The literal finite-aperture v2 Livšic coordinate is defined using norm-balanced deficiency
channels.  Reflection makes those two coefficients one common nonzero scalar.  This module
removes that scalar exactly: the projective characteristic is already the quotient of raw plus
and minus
deficiencies.  Thus a cofinal argument for the actual characteristic must control the paired raw
completed sources, rather than their individual normalizations.
-/

open Complex Metric Set Filter Topology

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

/-- Raw `+` coordinate of Suzuki's actual v2 characteristic. -/
def suzukiTaV2RawCharacteristicA (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  (z - I) * suzukiTaPhysicalFourier a (suzukiTaRawDeficiency a 1) z

/-- Raw `-` coordinate of Suzuki's actual v2 characteristic. -/
def suzukiTaV2RawCharacteristicE (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  (z + I) * suzukiTaPhysicalFourier a (suzukiTaRawDeficiency a (-1)) z

/-- The normalized `A` coordinate differs from its raw completed-source coordinate only by the
same scalar used by the `E` coordinate. -/
theorem suzukiTaV2CharacteristicA_eq_commonScale_raw
    (a : SuzukiPositiveAperture) :
    suzukiTaV2CharacteristicA a =
      fun z => (‖suzukiTaRawDeficiency a 1‖ : ℂ) * suzukiTaV2RawCharacteristicA a z := by
  funext z
  rw [suzukiTaV2CharacteristicA, suzukiTaPlusDeficiency,
    suzukiTaV2RawCharacteristicA, suzukiTaPhysicalFourier]
  rw [map_smul, suzukiApertureZeroExtendL2_smul,
    suzukiCompactL2Fourier_smul]
  rw [norm_suzukiTaRawDeficiency_neg_eq a 1]
  rw [suzukiTaPhysicalFourier]
  ring

/-- The normalized `E` coordinate has the same raw completed-source scalar as `A`. -/
theorem suzukiTaV2CharacteristicE_eq_commonScale_raw
    (a : SuzukiPositiveAperture) :
    suzukiTaV2CharacteristicE a =
      fun z => (‖suzukiTaRawDeficiency a 1‖ : ℂ) * suzukiTaV2RawCharacteristicE a z := by
  funext z
  rw [suzukiTaV2CharacteristicE, suzukiTaMinusDeficiency,
    suzukiTaV2RawCharacteristicE, suzukiTaPhysicalFourier]
  rw [map_smul, suzukiApertureZeroExtendL2_smul,
    suzukiCompactL2Fourier_smul]
  rw [suzukiTaPhysicalFourier]
  ring

/-- Exact de-normalization of Suzuki's actual v2 Livšic carrier.  No convergence, positivity,
or source estimate is assumed. -/
theorem suzukiTaV2Livsic_eq_rawDeficiency
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaV2Livsic a z =
      suzukiLivsicQuotient
        (suzukiTaV2RawCharacteristicA a)
        (suzukiTaV2RawCharacteristicE a) z := by
  rw [suzukiTaV2Livsic]
  rw [suzukiTaV2CharacteristicA_eq_commonScale_raw,
    suzukiTaV2CharacteristicE_eq_commonScale_raw]
  exact suzukiLivsicQuotient_common_scale _ _
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (suzukiTaRawDeficiency_ne_zero a 1)))

end RHTower

import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaDepthCharacterLadder
import GaloisForLFunctions.RHTower.RouteRRationalCartierPrimeDilationLanding

/-!
# Xi leading-jet parity cancels theta depth parity

The leading nonzero Xi coefficient changes under functional-equation reflection by `(-1)^m`,
where `m` is exact Xi multiplicity.  The terminal current of the actual theta root block changes
by `(-1)^(m-1)`.  Their product is therefore always `-1`, for every positive multiplicity.

Consequently a coefficient-faithful equation-Wronskian or leading-jet normalization is
reflection-odd unconditionally.  Its oddness cannot force the bare theta depth character to be
`-1`, hence cannot establish the first multiplicity-parity rung.
-/

open Complex

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Exact cancellation between leading-Xi-jet parity and terminal-theta-depth parity. -/
theorem xiJetParity_mul_thetaDepthCharacter_eq_neg_one
    (rho : XiDivisorSupport) :
    (-1 : ℂ) ^ xiSupportMultiplicity rho *
        thetaDepthCharacter (thetaSpectrumOfXiSupport rho) = -1 := by
  rw [thetaDepthCharacter_at_XiSupport]
  let m := xiSupportMultiplicity rho
  have hm : 0 < m := xiSupportMultiplicity_pos rho
  have hsucc : m = (m - 1) + 1 := by omega
  have hsquare :
      (-1 : ℂ) ^ (m - 1) * (-1 : ℂ) ^ (m - 1) = 1 := by
    rw [← pow_add]
    conv_lhs =>
      rw [show (m - 1) + (m - 1) = 2 * (m - 1) by omega]
    rw [pow_mul]
    norm_num
  change (-1 : ℂ) ^ m * (-1 : ℂ) ^ (m - 1) = -1
  rw [hsucc, pow_succ]
  calc
    ((-1 : ℂ) ^ (m - 1) * -1) * (-1 : ℂ) ^ (m - 1) =
        -( (-1 : ℂ) ^ (m - 1) * (-1 : ℂ) ^ (m - 1)) := by ring
    _ = -1 := by rw [hsquare]

/-- A leading-Xi-coefficient-weighted terminal theta current is reflection-odd for every
multiplicity.  The coefficient parity absorbs the exact parity character one seeks to detect. -/
theorem ccmRationalAdelicPrimeXiCartierCoefficient_reflection_mul_thetaDepthCharacter
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiCartierCoefficient (xiZeroReflectEquiv rho) *
        thetaDepthCharacter (thetaSpectrumOfXiSupport rho) =
      -ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  rw [ccmRationalAdelicPrimeXiCartierCoefficient_reflection]
  calc
    ((-1 : ℂ) ^ xiSupportMultiplicity rho *
          ccmRationalAdelicPrimeXiCartierCoefficient rho) *
        thetaDepthCharacter (thetaSpectrumOfXiSupport rho) =
      ((-1 : ℂ) ^ xiSupportMultiplicity rho *
          thetaDepthCharacter (thetaSpectrumOfXiSupport rho)) *
        ccmRationalAdelicPrimeXiCartierCoefficient rho := by ring
    _ = -ccmRationalAdelicPrimeXiCartierCoefficient rho := by
      rw [xiJetParity_mul_thetaDepthCharacter_eq_neg_one]
      ring

end

end RHTower.HedenmalmThetaSource

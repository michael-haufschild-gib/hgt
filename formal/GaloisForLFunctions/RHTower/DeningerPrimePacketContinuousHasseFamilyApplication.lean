import GaloisForLFunctions.RHTower.DeningerPrimeBlockHasseFamilyApplication
import GaloisForLFunctions.RHTower.DeningerPrimePacketContinuousHasse

/-!
# Continuous all-prime packet Hasse family

Continuous observations on arithmetic prime packets pass faithfully to canonical Haar-`L²`
fibres.  The resulting all-prime family separates global data modulo simultaneous packet
invisibility, exposing a direct local-place interface for Connes/Tate-style constructions.
-/

namespace RHTower

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous observations on every arithmetic prime packet form an all-prime Hasse family after
their faithful Haar-`L²` realization. -/
def deningerPrimePacketContinuousHaarHasseFamily
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ)) :
    GaloisForLFunctions.HTGeometry.HasseFamily
      (E ⧸ LinearMap.ker (deningerPrimeRestrictionLinearMap
        (deningerPrimePacketContinuousRestriction restriction)
        (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable)))
      Nat.Primes :=
  deningerPrimeBlockQuotientHasseFamily
    (deningerPrimePacketContinuousRestriction restriction)
    (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable)

end
end RHTower

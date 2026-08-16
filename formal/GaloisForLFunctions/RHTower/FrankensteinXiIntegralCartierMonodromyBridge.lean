import GaloisForLFunctions.RHTower.FrankensteinXiBidirectionalIntegralCartierSource
import GaloisForLFunctions.RHTower.FrankensteinSourceGammaCenteredMonodromyCartier
import GaloisForLFunctions.RHTower.FrankensteinBigWittIntegralBidirectionalGammaDescent

/-!
# Integral Cartier source bridge to monodromy, source naturality, and Big-Witt descent

The new integral conormal reporter is not an isolated endpoint.  This module proves exact
bidirectional bridges to three independently developed corpus routes:

* centered Hurwitz-log monodromy descent;
* genuine Calderón--Witt source/Gamma naturality;
* bidirectional integral Big-Witt Gamma ghosts.

Consequently a reporter on the new one-prime integral source class constructs all prior consumers,
while any prior source-natural reporter constructs the new one.  The bridge is unconditional; it
does not assert the common RH-strength existence premise.
-/

open Complex

namespace RHTower

noncomputable section

/-- Integral Cartier descent is exactly centered Hurwitz-monodromy descent. -/
theorem xiBidirectionalIntegralGammaReporter_iff_centeredLogCharacterDescends
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p) ↔
      XiCenteredLogCharacterDescends rho := by
  rw [deningerXiBidirectionalIntegralGammaReporter_nonempty_iff,
    xiCenteredLogCharacterDescends_iff_centeredRate_eq_zero,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Integral Cartier descent is exactly the rational Cartier landing at the same prime label. -/
theorem xiBidirectionalIntegralGammaReporter_iff_rationalCartierLanding
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p) ↔
      CCMRationalAdelicPrimeXiRationalCartierLanding p rho := by
  rw [xiBidirectionalIntegralGammaReporter_iff_centeredLogCharacterDescends,
    xiCenteredLogCharacterDescends_iff_rationalCartierLanding]

/-- Integral Cartier descent is exactly existence of the genuine two-prime source-natural Gamma
reporter.  The new source law removes the need to store a shared scalar, but adds no hidden premise. -/
theorem xiBidirectionalIntegralGammaReporter_iff_sourceGammaNaturalReporter
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p) ↔
      Nonempty (PrimeGammaTwoThreeSourceNaturalReporter
        (primeDepthBVWoldXiCenteredRate rho)) := by
  rw [xiBidirectionalIntegralGammaReporter_iff_centeredLogCharacterDescends,
    xiCenteredLogCharacterDescends_iff_sourceGammaNaturalReporter]

/-- Integral Cartier descent is exactly existence of the earlier integral Big-Witt pair. -/
theorem xiBidirectionalIntegralGammaReporter_iff_bigWittIntegralPair
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p) ↔
      Nonempty (PrimeGammaIntegralBidirectionalBigWittLift
        (primeDepthBVWoldXiCenteredRate rho)) := by
  rw [deningerXiBidirectionalIntegralGammaReporter_nonempty_iff,
    primeGammaIntegralBidirectionalBigWittLift_nonempty_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- One integral reporter constructs all coefficient-faithful consumers at once. -/
theorem xiBidirectionalIntegralGammaReporter_constructs_frankenstein_consumers
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (h : Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p)) :
    XiCenteredLogCharacterDescends rho ∧
      CCMRationalAdelicPrimeXiRationalCartierLanding p rho ∧
      Nonempty (PrimeGammaTwoThreeSourceNaturalReporter
        (primeDepthBVWoldXiCenteredRate rho)) ∧
      Nonempty (PrimeGammaIntegralBidirectionalBigWittLift
        (primeDepthBVWoldXiCenteredRate rho)) := by
  exact ⟨
    (xiBidirectionalIntegralGammaReporter_iff_centeredLogCharacterDescends rho p).1 h,
    (xiBidirectionalIntegralGammaReporter_iff_rationalCartierLanding rho p).1 h,
    (xiBidirectionalIntegralGammaReporter_iff_sourceGammaNaturalReporter rho p).1 h,
    (xiBidirectionalIntegralGammaReporter_iff_bigWittIntegralPair rho p).1 h⟩

/-- Genuine source/Gamma naturality constructs the new integral reporter at every retained prime
label. -/
theorem xiBidirectionalIntegralGammaReporter_of_sourceGammaNaturalReporter
    (rho : XiDivisorSupport)
    (h : Nonempty (PrimeGammaTwoThreeSourceNaturalReporter
      (primeDepthBVWoldXiCenteredRate rho)))
    (p : Nat.Primes) :
    Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p) :=
  (xiBidirectionalIntegralGammaReporter_iff_sourceGammaNaturalReporter rho p).2 h

end

end RHTower

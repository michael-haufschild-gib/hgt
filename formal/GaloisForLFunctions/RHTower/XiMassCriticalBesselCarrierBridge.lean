import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainderCells
import GaloisForLFunctions.RHTower.XiMassFourierBesselRightHalfPlane

/-!
# Literal Bessel realization of the critical Xi-mass prime kernel

The critical mass prime cone is built from the exponentially damped Fourier profile.  The
right-half-plane Fourier--Bessel continuation identifies every positive-height summand with the
deep-time mass-Bessel carrier, without an asymptotic replacement or a source hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

/-- Every positive-height critical Xi-mass atom is its literal deep-time Bessel carrier. -/
theorem xiMassCriticalDampedFourierProfile_eq_massBesselCarrier
    {a sigma u h : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (hh : 0 < h) :
    xiMassCriticalDampedFourierProfile a sigma u h =
      (Real.exp (-h / 2) : ℂ) * HTGeometry.massBesselCarrier a
        ((sigma : ℂ) + (u : ℂ) * I) h := by
  have hfreq : ((sigma : ℂ) + (u : ℂ) * I) ∈ xiMassBesselRightHalfPlane := by
    change 0 < (((sigma : ℂ) + (u : ℂ) * I)).re
    simpa using hsigma
  rw [xiMassCriticalDampedFourierProfile,
    stripFourier_xiMass_eq_massBesselCarrier ha hh hfreq]

end

end RHTower

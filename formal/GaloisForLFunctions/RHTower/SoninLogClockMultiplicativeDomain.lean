import GaloisForLFunctions.HTGeometry.FiniteClockMultiplicativeDomain
import GaloisForLFunctions.RHTower.SoninLogCoordinateScattering

/-!
# Multiplicative domain of the logarithmic Sonin clock

The finite-clock multiplicative-domain theorem specializes to logarithmic Fourier scattering.
The complete Sonin star-Kadison defect is the twirled master constraint of the observable
component erased by scattering, and it vanishes exactly on the scattering commutant.

Unlike the earlier squared Sonin Kadison defect, this result applies to arbitrary transition
operators: no self-adjointness, positivity, or physical-state hypothesis remains.
-/

namespace RHTower

noncomputable section

/-- Complete star-Kadison defect of the logarithmic Sonin clock-observer projection. -/
def soninLogFourierObservableTwirlStarKadisonDefect
    (X : SoninL2 →L[ℂ] SoninL2) : SoninL2 →L[ℂ] SoninL2 :=
  HTGeometry.finiteCyclicObservableTwirlStarKadisonDefect
    soninLogFourierScattering X 2

/-- The logarithmic Sonin observable twirl preserves adjoints for arbitrary operators. -/
theorem soninLogFourierObservableTwirl_adjoint
    (X : SoninL2 →L[ℂ] SoninL2) :
    (soninLogFourierObservableTwirl X).adjoint =
      soninLogFourierObservableTwirl X.adjoint := by
  simpa only [soninLogFourierObservableTwirl] using
    HTGeometry.finiteCyclicObservableTwirl_adjoint
      soninLogFourierScattering X 2 two_ne_zero
      soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one

/-- **Sonin operator-valued conditional variance.**  The complete clock defect is the Sonin
twirl of the master constraint of the scattering-erased observable component. -/
theorem soninLogFourierObservableTwirlStarKadisonDefect_eq_twirl_quantumMasterConstraint
    (X : SoninL2 →L[ℂ] SoninL2) :
    soninLogFourierObservableTwirlStarKadisonDefect X =
      soninLogFourierObservableTwirl
        (HTGeometry.quantumMasterConstraint
          (X - soninLogFourierObservableTwirl X)) := by
  simpa only [soninLogFourierObservableTwirlStarKadisonDefect,
    soninLogFourierObservableTwirl] using
      HTGeometry.finiteCyclicObservableTwirlStarKadisonDefect_eq_twirl_quantumMasterConstraint
        soninLogFourierScattering X 2 two_ne_zero
        soninLogFourierScattering_adjoint_mul_self
        soninLogFourierScattering_sq_eq_one

/-- The complete Sonin clock defect vanishes exactly when scattering erases no observable
component. -/
theorem soninLogFourierObservableTwirlStarKadisonDefect_eq_zero_iff_twirl_fixed
    (X : SoninL2 →L[ℂ] SoninL2) :
    soninLogFourierObservableTwirlStarKadisonDefect X = 0 ↔
      soninLogFourierObservableTwirl X = X := by
  simpa only [soninLogFourierObservableTwirlStarKadisonDefect,
    soninLogFourierObservableTwirl] using
      HTGeometry.finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_twirl_fixed
        soninLogFourierScattering X 2 two_ne_zero
        soninLogFourierScattering_adjoint_mul_self
        soninLogFourierScattering_sq_eq_one

/-- **Sonin multiplicative-domain theorem.**  For every bounded operator, zero complete
conditional variance is equivalent to commutation with logarithmic Fourier scattering. -/
theorem soninLogFourierObservableTwirlStarKadisonDefect_eq_zero_iff_commutes
    (X : SoninL2 →L[ℂ] SoninL2) :
    soninLogFourierObservableTwirlStarKadisonDefect X = 0 ↔
      soninLogFourierScattering * X = X * soninLogFourierScattering := by
  simpa only [soninLogFourierObservableTwirlStarKadisonDefect] using
    HTGeometry.finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_commutes
      soninLogFourierScattering X 2 two_ne_zero
      soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one

end

end RHTower

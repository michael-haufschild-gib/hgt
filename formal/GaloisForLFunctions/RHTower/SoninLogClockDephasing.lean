import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockDephasing
import GaloisForLFunctions.RHTower.SoninLogCoordinateScattering

/-!
# Static dephasing identity for the logarithmic Sonin clock

The relational-clock double commutator specializes to logarithmic Fourier scattering.  It is
exactly four times the observable component erased by the Sonin clock twirl.  Consequently its
kernel is the scattering commutant with no self-adjointness hypothesis on the observable.

This is a value relation in the constrained observer algebra, not a claim that scattering is a
temporal evolution.
-/

namespace RHTower

noncomputable section

/-- The logarithmic Sonin clock double commutator. -/
def soninLogFourierDoubleCommutator
    (X : SoninL2 →L[ℂ] SoninL2) : SoninL2 →L[ℂ] SoninL2 :=
  HTGeometry.finiteInvolutiveClockDoubleCommutator
    soninLogFourierScattering X

/-- **Sonin relational-clock dephasing identity.**  The double scattering commutator is exactly
four times the observable information erased by the logarithmic clock. -/
theorem soninLogFourierDoubleCommutator_eq_four_smul_disturbance
    (X : SoninL2 →L[ℂ] SoninL2) :
    soninLogFourierDoubleCommutator X =
      (4 : ℂ) • (X - soninLogFourierObservableTwirl X) := by
  simpa only [soninLogFourierDoubleCommutator, soninLogFourierObservableTwirl] using
    HTGeometry.finiteInvolutiveClockDoubleCommutator_eq_four_smul_disturbance
      soninLogFourierScattering X soninLogFourierScattering_sq_eq_one

/-- The logarithmic Sonin double commutator detects the entire scattering commutant without a
self-adjointness, positivity, or physical-state premise. -/
theorem soninLogFourierDoubleCommutator_eq_zero_iff_commutes
    (X : SoninL2 →L[ℂ] SoninL2) :
    soninLogFourierDoubleCommutator X = 0 ↔
      soninLogFourierScattering * X = X * soninLogFourierScattering := by
  simpa only [soninLogFourierDoubleCommutator] using
    HTGeometry.finiteInvolutiveClockDoubleCommutator_eq_zero_iff_commutes
      soninLogFourierScattering X soninLogFourierScattering_sq_eq_one

/-- An observable survives logarithmic-clock coarse-graining exactly when it commutes with
Fourier scattering.  This is the premise-free conditional-expectation criterion underlying the
double-commutator theorem. -/
theorem soninLogFourierObservableTwirl_eq_self_iff_commutes
    (X : SoninL2 →L[ℂ] SoninL2) :
    soninLogFourierObservableTwirl X = X ↔
      soninLogFourierScattering * X = X * soninLogFourierScattering := by
  constructor
  · intro hfixed
    apply (HTGeometry.sub_finiteInvolutiveObservableTwirl_eq_zero_iff_commutes
      soninLogFourierScattering X soninLogFourierScattering_sq_eq_one).mp
    have hzero : X - soninLogFourierObservableTwirl X = 0 := by
      rw [hfixed, sub_self]
    simpa only [soninLogFourierObservableTwirl] using hzero
  · intro hcomm
    have hzero :=
      (HTGeometry.sub_finiteInvolutiveObservableTwirl_eq_zero_iff_commutes
        soninLogFourierScattering X soninLogFourierScattering_sq_eq_one).mpr hcomm
    exact (sub_eq_zero.mp hzero).symm

end

end RHTower

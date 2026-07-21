import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockQuantumFisherDephasing
import GaloisForLFunctions.HTGeometry.QuantumFisherClockReparametrization
import GaloisForLFunctions.RHTower.SoninLogClockDephasing

/-!
# Quantum Fisher value of the logarithmic Sonin clock

The general finite-clock QFI/observability identity specializes to logarithmic Fourier
scattering.  On a normalized physical Sonin state, the tangent erased by the invariant-sector
average is automatically orthogonal to the state.  Its pure-state QFI is therefore both four
times the Sonin clock Kadison defect and exactly the squared scattering--observable commutator.

This is a static relation on the constrained observer algebra.  It does not treat logarithmic
scattering as temporal evolution.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- The pure-state QFI hidden by the logarithmic Sonin clock is four times its static
observability variance.  Physicality discharges the projective-overlap term. -/
theorem soninLogClock_erasedPureStateQuantumFisherValue_eq_four_mul_observabilityVariance
    (X : SoninL2 →L[ℂ] SoninL2) (hX : IsSelfAdjoint X)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ) :
    HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
        (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ 2) =
      4 * Complex.re
        (inner ℂ ψ (soninLogFourierObservableTwirlKadisonDefect X ψ)) := by
  rw [GaloisForLFunctions.PhysicalState] at hψ
  have hfixed : soninLogFourierScattering ψ = ψ := by
    apply sub_eq_zero.mp
    simpa using hψ
  simpa only [soninLogFourierInvariantAverage,
    soninLogFourierObservableTwirlKadisonDefect,
    HTGeometry.finiteInvolutiveObservableTwirlKadisonDefect] using
      (HTGeometry.finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_observabilityVariance
        soninLogFourierScattering X 2 two_ne_zero
        soninLogFourierScattering_adjoint_mul_self
        soninLogFourierScattering_sq_eq_one hX hψnorm hfixed)

/-- The Sonin hidden-clock QFI/variance identity is an equality of coordinate-free clock line
values.  The observer algebra fixes the visible tangent while `clockIncrement` records an arbitrary
local clock calibration. -/
theorem soninLogClock_erasedQuantumFisherClockLineValue_eq_observabilityLineValue
    (X : SoninL2 →L[ℂ] SoninL2) (hX : IsSelfAdjoint X)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ)
    (clockIncrement : ℝ) :
    HTGeometry.quantumFisherClockLineValue (‖ψ‖ ^ 2)
        (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
        (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ 2)
        clockIncrement =
      HTGeometry.finiteClockObservabilityLineValue
        (Complex.re
          (inner ℂ ψ (soninLogFourierObservableTwirlKadisonDefect X ψ)))
        clockIncrement := by
  rw [GaloisForLFunctions.PhysicalState] at hψ
  have hfixed : soninLogFourierScattering ψ = ψ := by
    apply sub_eq_zero.mp
    simpa using hψ
  simpa only [soninLogFourierInvariantAverage,
    soninLogFourierObservableTwirlKadisonDefect,
    HTGeometry.finiteInvolutiveObservableTwirlKadisonDefect] using
      (HTGeometry.finiteClock_erasedQuantumFisherClockLineValue_eq_observabilityLineValue
        soninLogFourierScattering X 2 two_ne_zero
        soninLogFourierScattering_adjoint_mul_self
        soninLogFourierScattering_sq_eq_one hX hψnorm hfixed clockIncrement)

/-- **Sonin clock QFI/commutator identity.**  On the physical constraint surface, the entire
hidden-clock QFI is the squared scattering--observable commutator.  Consequently no independent
QFI-overlap, positivity, or commutator-energy conversion hypothesis remains. -/
theorem soninLogClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
    (X : SoninL2 →L[ℂ] SoninL2) (hX : IsSelfAdjoint X)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ) :
    HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
        (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ 2) =
      ‖((X * soninLogFourierScattering - soninLogFourierScattering * X) :
        SoninL2 →L[ℂ] SoninL2) ψ‖ ^ 2 := by
  rw [soninLogClock_erasedPureStateQuantumFisherValue_eq_four_mul_observabilityVariance
    X hX hψnorm hψ]
  rw [re_inner_soninLogFourierObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq
    X hX.star_eq hψ]
  ring

/-- **Sonin QFI/dephasing identity.**  On a normalized physical state, the QFI hidden by the
logarithmic clock is one quarter of the squared double-scattering-commutator value.  This applies
the relational-clock dephasing relation directly to the existing Sonin QFI corpus. -/
theorem soninLogClock_erasedPureStateQuantumFisherValue_eq_quarter_doubleCommutatorNormSq
    (X : SoninL2 →L[ℂ] SoninL2) (hX : IsSelfAdjoint X)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ) :
    HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
        (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ 2) =
      (4 : ℝ)⁻¹ * ‖soninLogFourierDoubleCommutator X ψ‖ ^ 2 := by
  rw [GaloisForLFunctions.PhysicalState] at hψ
  have hfixed : soninLogFourierScattering ψ = ψ := by
    apply sub_eq_zero.mp
    simpa using hψ
  simpa only [soninLogFourierInvariantAverage, soninLogFourierDoubleCommutator] using
    HTGeometry.finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_quarter_doubleCommutatorNormSq
      soninLogFourierScattering X soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one hX hψnorm hfixed

end

end RHTower

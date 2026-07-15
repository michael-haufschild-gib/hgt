import GaloisForLFunctions.HTGeometry.FiniteClockQuantumFisher
import GaloisForLFunctions.RHTower.SoninLogCoordinateScattering

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

end

end RHTower

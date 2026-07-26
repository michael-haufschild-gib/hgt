import GaloisForLFunctions.HTGeometry.InvolutiveClockFidelityFisherSectorFactorizationUniversalityLaw
import GaloisForLFunctions.RHTower.SoninLogClockFidelityAsymmetry
import GaloisForLFunctions.RHTower.SoninLogClockQuantumFisher

/-!
# Sonin logarithmic-clock fidelity--Fisher sector factorization

The abstract involutive-clock factorization identifies Fourier-scattering infidelity of every
observed physical Sonin state with invariant-sector mass times hidden logarithmic-clock QFI.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- **Sonin fidelity--Fisher sector-factorization law.**  On a normalized physical state, every
bounded observation has homogeneous logarithmic-scattering infidelity equal to its invariant
Sonin-sector weight times its erased logarithmic-clock quantum Fisher value. -/
theorem soninLogClock_homogeneousFidelityDeficit_eq_invariantWeight_mul_erasedQFI
    (X : SoninL2 →L[ℂ] SoninL2)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ) :
    ‖X ψ‖ ^ 4 -
        ‖inner ℂ (X ψ) (soninLogFourierScattering (X ψ))‖ ^ 2 =
      ‖soninLogFourierInvariantAverage (X ψ)‖ ^ 2 *
        HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ 2)
          (‖inner ℂ ψ
            ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
          (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ 2) := by
  have hfixed : soninLogFourierScattering ψ = ψ := by
    rw [GaloisForLFunctions.PhysicalState] at hψ
    apply sub_eq_zero.mp
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using hψ
  simpa only [soninLogFourierInvariantAverage] using
    HTGeometry.finiteInvolutiveClock_homogeneousFidelityDeficit_eq_invariantWeight_mul_erasedQFI
      soninLogFourierScattering X soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one hψnorm hfixed

end

end RHTower

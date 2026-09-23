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
    ‖X ψ‖ ^ (4 : ℕ) -
        ‖inner ℂ (X ψ) (soninLogFourierScattering (X ψ))‖ ^ (2 : ℕ) =
      ‖soninLogFourierInvariantAverage (X ψ)‖ ^ (2 : ℕ) *
        HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ (2 : ℕ))
          (‖inner ℂ ψ
            ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
          (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ (2 : ℕ)) := by
  have hcomm :
      ((X * soninLogFourierScattering - soninLogFourierScattering * X) :
          SoninL2 →L[ℂ] SoninL2) ψ =
        (2 : ℂ) • ((1 - soninLogFourierInvariantAverage) (X ψ)) := by
    have hfixed : soninLogFourierScattering ψ = ψ := by
      rw [GaloisForLFunctions.PhysicalState] at hψ
      change (soninLogFourierScattering - 1) ψ = 0 at hψ
      apply sub_eq_zero.mp
      simpa only [_root_.sub_apply, one_apply_eq_self] using hψ
    rw [_root_.sub_apply, mul_apply_eq_comp,
      mul_apply_eq_comp, hfixed, _root_.sub_apply,
      one_apply_eq_self, soninLogFourierInvariantAverage,
      HTGeometry.finiteInvolutiveGaugeAverage_apply]
    norm_num
    module
  rw [soninLogFourierScattering_homogeneousFidelityDeficit_eq_four_mul_sectorWeights,
    soninLogClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
      X hψnorm hψ,
    hcomm, norm_smul]
  norm_num
  ring

end

end RHTower

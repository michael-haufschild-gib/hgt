import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsAccumulatedInformation
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFourierObservability

/-!
# Exact Fourier energy of arbitrary Gibbs populations

The critical thermal kernel extracted from arXiv:2609.00025 retains five
Fourier modes. The corpus QFT Parseval theorem turns this into a complete
positive-time energy formula for every finite Gibbs energy landscape.
-/

namespace GaloisForLFunctions.HTGeometry
open scoped Matrix
noncomputable section

/-- Mass normalization fixes the invariant Gibbs Fourier moment exactly. -/
theorem egbFixedChargeAGibbsFourierMoment_zero (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsFourierMoment n β E 0 = QuantumAlg.invSqrtN (n + 3) := by
  unfold egbFixedChargeAGibbsFourierMoment
  change egbFixedChargeACriticalFourierCoordinates n
    (fun i => (_root_.HTGeometry.finiteGibbsStateWeight β E i : ℂ)) 0 = _
  rw [egbFixedChargeACriticalFourierCoordinates_zero_frequency,
    ← Complex.ofReal_sum, _root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one,
    Complex.ofReal_one, mul_one]

/-- The invariant Fourier energy is precisely the uniform collision floor. -/
theorem egbFixedChargeAGibbsFourierMoment_zero_sq_norm (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ‖egbFixedChargeAGibbsFourierMoment n β E 0‖ ^ 2 = ((2 : ℝ) ^ (n + 3))⁻¹ := by
  rw [egbFixedChargeAGibbsFourierMoment_zero, QuantumAlg.norm_invSqrtN,
    inv_pow (Real.sqrt ((2 : ℝ) ^ (n + 3))) 2, Real.sq_sqrt (by positivity)]

/-- At every positive time, the full Gibbs collision probability has five exact spectral terms. -/
theorem egbFixedChargeAGibbsMarkovPopulation_spectral_energy (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ∑ i, egbFixedChargeAGibbsMarkovPopulation n (m + 1) β E i ^ 2 =
      ∑ k : Fin 5, (egbFixedChargeACriticalMarkovEigenvalues k ^ (m + 1)) ^ 2 *
        ‖egbFixedChargeAGibbsFourierMoment n β E k‖ ^ 2 := by
  have h := egbFixedChargeACriticalMarkovMatrix_five_mode_energy n m
    (fun i => (_root_.HTGeometry.finiteGibbsStateWeight β E i : ℂ))
  rw [egbFixedChargeACriticalMarkov_complex_lift] at h
  simpa only [egbFixedChargeAGibbsMarkovPopulation, egbFixedChargeAGibbsFourierMoment,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

end
end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFourierObservability
import GaloisForLFunctions.QuantumAlg.NoetherCorpusApplications

/-!
The corpus Noether norm law for the quantum Fourier transform supplies Parseval
coordinates for the critical kernel derived from arXiv:2609.00025.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg
open scoped Matrix
noncomputable section

/-- Full Fourier analysis preserves the Hilbert norm, by the existing QFT Noether law. -/
theorem egbFixedChargeACriticalFourierCoordinates_norm (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℂ) :
    ‖(WithLp.toLp 2 (egbFixedChargeACriticalFourierCoordinates n f) :
      EuclideanSpace ℂ (Fin (2 ^ (n + 3))))‖ =
        ‖(WithLp.toLp 2 f : EuclideanSpace ℂ (Fin (2 ^ (n + 3))))‖ := by
  have h := noetherFirst_qftNorm (n + 3)
    (WithLp.toLp 2 (egbFixedChargeACriticalFourierCoordinates n f))
  change ‖(WithLp.toLp 2 (QFTMatrix (n + 3) *ᵥ egbFixedChargeACriticalFourierCoordinates n f) :
      EuclideanSpace ℂ (Fin (2 ^ (n + 3))))‖ = _ at h
  rw [egbFixedChargeACriticalFourierCoordinates_inverse] at h
  exact h.symm

/-- Parseval's identity is exact for every complex input on the critical grid. -/
theorem egbFixedChargeACriticalFourierCoordinates_parseval (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℂ) :
    ∑ j, ‖egbFixedChargeACriticalFourierCoordinates n f j‖ ^ (2 : ℕ) = ∑ i, ‖f i‖ ^ (2 : ℕ) := by
  have h := congrArg (fun r : ℝ => r ^ (2 : ℕ)) (egbFixedChargeACriticalFourierCoordinates_norm n f)
  simp only [EuclideanSpace.norm_eq] at h
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h
  exact h

/-- The output squared norm is the exact spectral sum of the damped Fourier coordinates. -/
theorem egbFixedChargeACriticalMarkovMatrix_spectral_energy (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℂ) :
    ∑ i, ‖((egbFixedChargeACriticalMarkovMatrix n ^ m) *ᵥ f) i‖ ^ (2 : ℕ) =
      ∑ j, ‖egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues j ^ m *
        egbFixedChargeACriticalFourierCoordinates n f j‖ ^ (2 : ℕ) := by
  rw [← egbFixedChargeACriticalFourierCoordinates_parseval,
    egbFixedChargeACriticalFourierCoordinates_evolution]

end
end GaloisForLFunctions.HTGeometry

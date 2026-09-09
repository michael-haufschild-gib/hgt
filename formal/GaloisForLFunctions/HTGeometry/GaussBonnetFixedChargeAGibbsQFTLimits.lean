import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalQFTSpectrum
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsGramLimits

/-!
Fourier-coordinate convergence of the actual normalized Gibbs matrix from
arXiv:2609.00025. The finite-state matrix approaches its explicit five-mode
critical diagonal faster than the phase-asymmetry parameter.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg Filter Topology

noncomputable section

/-- Actual Gibbs Gram represented in the corpus QFT coordinates. -/
def egbFixedChargeAGibbsQFTMatrix (w φ τ l₁ l₂ : ℝ) (n : ℕ) :
    Matrix (Fin (2 ^ (n + 3))) (Fin (2 ^ (n + 3))) ℂ :=
  star (QFTMatrix (n + 3)) *
    egbFixedChargeAGibbsGram w φ τ l₁ l₂ (2 ^ (n + 3))
      (egbFixedChargeAFourierGrid (n + 3)) * QFTMatrix (n + 3)

/-- Fourier coordinates expose the exact critical five-mode diagonal. -/
theorem egbFixedChargeAGibbsQFTMatrix_critical_limit
    (w φ l₁ l₂ : ℝ) (n : ℕ) :
    Tendsto (fun τ : ℝ => egbFixedChargeAGibbsQFTMatrix w φ τ l₁ l₂ n) atBot
      (𝓝 (Matrix.diagonal (egbFixedChargeACriticalFourierSpectrum n))) := by
  have hg := egbFixedChargeAGibbsGram_critical_limit w φ l₁ l₂ (2 ^ (n + 3))
    (egbFixedChargeAFourierGrid (n + 3))
  have hl : Tendsto (fun _ : ℝ => star (QFTMatrix (n + 3))) atBot
      (𝓝 (star (QFTMatrix (n + 3)))) := tendsto_const_nhds
  have hr : Tendsto (fun _ : ℝ => QFTMatrix (n + 3)) atBot
      (𝓝 (QFTMatrix (n + 3))) := tendsto_const_nhds
  have h := (hl.mul hg).mul hr
  rw [← egbFixedChargeACriticalGram_QFT_diagonalization]
  exact h

/-- The transformed first correction equals the QFT transform of the Gram correction. -/
theorem egbFixedChargeAGibbsQFTMatrix_correction_identity
    (w φ τ l₁ l₂ : ℝ) (n : ℕ) :
    (egbCoexistenceASymmetricRatio τ : ℂ)⁻¹ •
      (egbFixedChargeAGibbsQFTMatrix w φ τ l₁ l₂ n -
        Matrix.diagonal (egbFixedChargeACriticalFourierSpectrum n)) =
      star (QFTMatrix (n + 3)) *
        egbFixedChargeAGibbsGramCorrection w φ τ l₁ l₂ (2 ^ (n + 3))
          (egbFixedChargeAFourierGrid (n + 3)) * QFTMatrix (n + 3) := by
  rw [← egbFixedChargeACriticalGram_QFT_diagonalization]
  simp only [egbFixedChargeAGibbsQFTMatrix, egbFixedChargeAGibbsGramCorrection,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

/-- Both spectral-weight errors and off-diagonal couplings vanish faster than asymmetry. -/
theorem egbFixedChargeAGibbsQFTMatrix_first_zero_limit
    (w φ l₁ l₂ : ℝ) (n : ℕ) :
    Tendsto (fun τ : ℝ => (egbCoexistenceASymmetricRatio τ : ℂ)⁻¹ •
      (egbFixedChargeAGibbsQFTMatrix w φ τ l₁ l₂ n -
        Matrix.diagonal (egbFixedChargeACriticalFourierSpectrum n))) atBot (𝓝 0) := by
  have hg := egbFixedChargeAGibbsGramCorrection_zero_limit w φ l₁ l₂ (2 ^ (n + 3))
    (egbFixedChargeAFourierGrid (n + 3))
  have hl : Tendsto (fun _ : ℝ => star (QFTMatrix (n + 3))) atBot
      (𝓝 (star (QFTMatrix (n + 3)))) := tendsto_const_nhds
  have hr : Tendsto (fun _ : ℝ => QFTMatrix (n + 3)) atBot
      (𝓝 (QFTMatrix (n + 3))) := tendsto_const_nhds
  have h := (hl.mul hg).mul hr
  simpa only [egbFixedChargeAGibbsQFTMatrix_correction_identity, Matrix.mul_zero,
    Matrix.zero_mul] using h

/-- Each of the five occupied diagonal entries approaches its explicit positive weight. -/
theorem egbFixedChargeAGibbsQFTMatrix_mode_limit
    (w φ l₁ l₂ : ℝ) (n : ℕ) (k : Fin 5) :
    Tendsto (fun τ : ℝ => egbFixedChargeAGibbsQFTMatrix w φ τ l₁ l₂ n
      (egbFixedChargeAFiveFourierModes n k) (egbFixedChargeAFiveFourierModes n k)) atBot
      (𝓝 (((2 : ℝ) ^ (n + 3) * egbFixedChargeAFourierWeights k : ℂ))) := by
  have h := egbFixedChargeAGibbsQFTMatrix_critical_limit w φ l₁ l₂ n
  have he := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h
    (egbFixedChargeAFiveFourierModes n k)) (egbFixedChargeAFiveFourierModes n k)
  simpa only [Matrix.diagonal_apply_eq, egbFixedChargeACriticalFourierSpectrum_mode] using he

end

end GaloisForLFunctions.HTGeometry

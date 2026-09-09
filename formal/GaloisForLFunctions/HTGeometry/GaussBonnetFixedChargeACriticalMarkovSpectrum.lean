import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovKernel
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAFiveModeDynamics

/-!
The exact Markov spectrum exposed by the critical Gibbs kernel of arXiv:2609.00025:
1, 2/3, 1/6, 1/6, 2/3, with all remaining frequencies zero.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg
open scoped Matrix

noncomputable section

/-- Dimension-free eigenvalues of the normalized critical Gibbs Markov chain. -/
def egbFixedChargeACriticalMarkovEigenvalues : Fin 5 → ℝ :=
  ![1, 2 / 3, 1 / 6, 1 / 6, 2 / 3]

/-- Markov normalization rescales the previous Gibbs Fourier coefficients exactly. -/
theorem egbFixedChargeACriticalMarkovEigenvalues_formula (k : Fin 5) :
    egbFixedChargeACriticalMarkovEigenvalues k =
      (8 / 3) * egbFixedChargeAFourierWeights k := by
  fin_cases k <;> norm_num [egbFixedChargeACriticalMarkovEigenvalues, egbFixedChargeAFourierWeights]

/-- Normalized spectral weights agree with the scaled critical Gibbs spectrum. -/
theorem egbFixedChargeACriticalMarkovSpectrum_normalization
    (n : ℕ) (j : Fin (2 ^ (n + 3))) :
    egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues j =
      ((8 / (3 * (2 : ℝ) ^ (n + 3)) : ℝ) : ℂ) * egbFixedChargeACriticalFourierSpectrum n j := by
  classical
  simp only [egbFixedChargeAFiveModeSpectrum, egbFixedChargeACriticalFourierSpectrum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [egbFixedChargeACriticalMarkovEigenvalues_formula]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  field_simp

/-- The transition matrix represented over the complex field for QFT analysis. -/
def egbFixedChargeACriticalMarkovMatrix (n : ℕ) :
    Matrix (Fin (2 ^ (n + 3))) (Fin (2 ^ (n + 3))) ℂ :=
  Matrix.of fun i j => (egbFixedChargeACriticalMarkovWeight n i j : ℂ)

/-- The corpus Markov operator is exactly the five-mode quantum Fourier multiplier. -/
theorem egbFixedChargeACriticalMarkovMatrix_QFT (n : ℕ) :
    egbFixedChargeACriticalMarkovMatrix n =
      egbFixedChargeAQFTMultiplier (n + 3)
        (egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues) := by
  have hn := funext (egbFixedChargeACriticalMarkovSpectrum_normalization n)
  rw [hn, egbFixedChargeAQFTMultiplier_real_scale,
    ← egbFixedChargeACriticalGram_QFT_multiplier]
  ext i j
  simp only [egbFixedChargeACriticalMarkovMatrix, egbFixedChargeACriticalMarkovWeight,
    egbFixedChargeACriticalGram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]

/-- Every positive number of Markov steps has explicit powered spectral coefficients. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_QFT (n m : ℕ) :
    egbFixedChargeACriticalMarkovMatrix n ^ (m + 1) =
      egbFixedChargeAQFTMultiplier (n + 3)
        (egbFixedChargeAFiveModeSpectrum n
          (fun k => egbFixedChargeACriticalMarkovEigenvalues k ^ (m + 1))) := by
  rw [egbFixedChargeACriticalMarkovMatrix_QFT, egbFixedChargeAFiveModeSpectrum_matrix_pow]

/-- The real-kernel action and the QFT matrix action are the same operator on complex profiles. -/
theorem egbFixedChargeACriticalMarkovMatrix_apply
    (n : ℕ) (f : Fin (2 ^ (n + 3)) → ℂ) :
    egbFixedChargeACriticalMarkovMatrix n *ᵥ f =
      (egbFixedChargeACriticalMarkovKernel n).toFinitePositiveKernel.applyComplex f := rfl

end

end GaloisForLFunctions.HTGeometry

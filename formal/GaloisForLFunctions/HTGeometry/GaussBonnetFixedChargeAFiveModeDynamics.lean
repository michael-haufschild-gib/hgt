import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAFourierCharacterProjectors
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQFTDynamics

/-!
Reusable exact dynamics on the five Fourier modes exposed by the critical Gibbs
kernel of arXiv:2609.00025. Arbitrary real coefficients are allowed; the following
Markov application will supply its own concrete contraction coefficients.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg

noncomputable section

/-- A spectrum supported on the five nonaliased critical harmonics. -/
def egbFixedChargeAFiveModeSpectrum (n : ℕ) (a : Fin 5 → ℝ)
    (j : Fin (2 ^ (n + 3))) : ℂ :=
  ∑ k : Fin 5, (a k : ℂ) * (Pi.single (egbFixedChargeAFiveFourierModes n k)
    (1 : ℂ) : Fin (2 ^ (n + 3)) → ℂ) j

/-- Each chosen frequency retains exactly its assigned coefficient. -/
theorem egbFixedChargeAFiveModeSpectrum_mode
    (n : ℕ) (a : Fin 5 → ℝ) (k : Fin 5) :
    egbFixedChargeAFiveModeSpectrum n a (egbFixedChargeAFiveFourierModes n k) = (a k : ℂ) := by
  classical
  simp [egbFixedChargeAFiveModeSpectrum, Pi.single_apply,
    (egbFixedChargeAFiveFourierModes_injective n).eq_iff]

/-- Positive integer powers preserve the five-mode support exactly. -/
theorem egbFixedChargeAFiveModeSpectrum_pow
    (n m : ℕ) (a : Fin 5 → ℝ) (j : Fin (2 ^ (n + 3))) :
    egbFixedChargeAFiveModeSpectrum n a j ^ (m + 1) =
      egbFixedChargeAFiveModeSpectrum n (fun k => a k ^ (m + 1)) j := by
  classical
  by_cases h : ∃ k : Fin 5, j = egbFixedChargeAFiveFourierModes n k
  · obtain ⟨k, rfl⟩ := h
    simp only [egbFixedChargeAFiveModeSpectrum_mode, Complex.ofReal_pow]
  · have hn : ∀ k : Fin 5, egbFixedChargeAFiveFourierModes n k ≠ j := by
      intro k hk
      exact h ⟨k, hk.symm⟩
    simp [egbFixedChargeAFiveModeSpectrum, Pi.single_apply, hn]

/-- Exact Laurent formula for any five-mode multiplier, with its grid-size normalization. -/
theorem egbFixedChargeAFiveModeSpectrum_scaled_entry
    (n : ℕ) (a : Fin 5 → ℝ) (i j : Fin (2 ^ (n + 3))) :
    ((2 : ℝ) ^ (n + 3) : ℂ) *
      egbFixedChargeAQFTMultiplier (n + 3) (egbFixedChargeAFiveModeSpectrum n a) i j =
        ∑ k : Fin 5, (a k : ℂ) * egbFixedChargeAFourierCharacter (n + 3) i j ^
          (egbFixedChargeAFiveFourierModes n k).val := by
  classical
  rw [egbFixedChargeAQFTMultiplier_entry]
  simp only [egbFixedChargeAFiveModeSpectrum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Pi.single_apply]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  calc
    _ = (a k : ℂ) * (((2 : ℝ) ^ (n + 3) : ℂ) *
      QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n k) *
      star (QFTMatrix (n + 3) j (egbFixedChargeAFiveFourierModes n k))) := by ring
    _ = _ := by rw [egbFixedChargeAFourierCharacter_projector]

/-- Positive powers of a five-mode Fourier operator are explicit again. -/
theorem egbFixedChargeAFiveModeSpectrum_matrix_pow
    (n m : ℕ) (a : Fin 5 → ℝ) :
    egbFixedChargeAQFTMultiplier (n + 3) (egbFixedChargeAFiveModeSpectrum n a) ^ (m + 1) =
      egbFixedChargeAQFTMultiplier (n + 3)
        (egbFixedChargeAFiveModeSpectrum n (fun k => a k ^ (m + 1))) := by
  rw [egbFixedChargeAQFTMultiplier_pow]
  simp only [egbFixedChargeAFiveModeSpectrum_pow]

end

end GaloisForLFunctions.HTGeometry

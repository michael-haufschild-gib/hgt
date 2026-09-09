import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAFourierCharacterProjectors

/-!
Exact five-mode QFT spectrum of the critical Gibbs Gram derived from
arXiv:2609.00025. The critical profile comes from the actual normalized Gibbs
barrier; its universal rank-five ceiling is attained on every grid here.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg

noncomputable section

/-- The critical Gibbs Gram is the QFT multiplier with the five explicit weights. -/
theorem egbFixedChargeACriticalGram_QFT_multiplier (n : ℕ) :
    egbFixedChargeACriticalGram (2 ^ (n + 3)) (egbFixedChargeAFourierGrid (n + 3)) =
      egbFixedChargeAQFTMultiplier (n + 3) (egbFixedChargeACriticalFourierSpectrum n) := by
  classical
  ext i j
  symm
  rw [egbFixedChargeAQFTMultiplier_entry]
  simp only [egbFixedChargeACriticalFourierSpectrum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k : Fin 5, ((2 : ℝ) ^ (n + 3) * egbFixedChargeAFourierWeights k : ℂ) *
        QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n k) *
        star (QFTMatrix (n + 3) j (egbFixedChargeAFiveFourierModes n k)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp [Pi.single_apply]
    _ = ∑ k : Fin 5, (egbFixedChargeAFourierWeights k : ℂ) *
        egbFixedChargeAFourierCharacter (n + 3) i j ^
          (egbFixedChargeAFiveFourierModes n k).val := by
      apply Finset.sum_congr rfl
      intro k _
      calc
        _ = (egbFixedChargeAFourierWeights k : ℂ) *
            (((2 : ℝ) ^ (n + 3) : ℂ) *
              QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n k) *
              star (QFTMatrix (n + 3) j (egbFixedChargeAFiveFourierModes n k))) := by
          ring
        _ = _ := by rw [egbFixedChargeAFourierCharacter_projector]
    _ = _ := by
      have hm (k : Fin 5) := congrFun (egbFixedChargeAFourierCharacter_modes n i j) k
      simp only [hm, egbFixedChargeAFourierWeights, Fin.sum_univ_succ,
        Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
      rw [egbFixedChargeACriticalGram_fourier_entry]
      ring

/-- Existing QFT diagonalizes the critical Gibbs matrix exactly. -/
theorem egbFixedChargeACriticalGram_QFT_diagonalization (n : ℕ) :
    star (QFTMatrix (n + 3)) *
      egbFixedChargeACriticalGram (2 ^ (n + 3)) (egbFixedChargeAFourierGrid (n + 3)) *
      QFTMatrix (n + 3) = Matrix.diagonal (egbFixedChargeACriticalFourierSpectrum n) := by
  rw [egbFixedChargeACriticalGram_QFT_multiplier,
    egbFixedChargeAQFTMultiplier_diagonalization]

/-- The universal rank-five bound is sharp on every dyadic grid with at least eight points. -/
theorem egbFixedChargeACriticalGram_QFT_rank_five (n : ℕ) :
    (egbFixedChargeACriticalGram (2 ^ (n + 3))
      (egbFixedChargeAFourierGrid (n + 3))).rank = 5 := by
  rw [egbFixedChargeACriticalGram_QFT_multiplier, egbFixedChargeAQFTMultiplier_rank,
    egbFixedChargeACriticalFourierSpectrum_card]

end

end GaloisForLFunctions.HTGeometry

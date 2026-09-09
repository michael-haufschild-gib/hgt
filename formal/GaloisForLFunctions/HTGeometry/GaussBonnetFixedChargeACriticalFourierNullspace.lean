import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsEntropyRates

/-!
The critical kernel derived from arXiv:2609.00025 has a large exact Fourier nullspace.
These are mathematical consequences of its five-mode spectrum, not an additional
physical evolution postulate.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg
open scoped Matrix
noncomputable section

private theorem first_qft_entry_ne_zero (n : ℕ) (j : Fin (2 ^ (n + 3))) :
    QFTMatrix (n + 3) 0 j ≠ 0 := by
  have hn : invSqrtN (n + 3) ≠ 0 := by
    unfold invSqrtN
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt
      (Real.sqrt_pos.mpr (pow_pos (by norm_num) _))))
  simpa only [QFT_entry, Fin.val_zero, Nat.zero_mul, pow_zero, mul_one] using hn

/-- Every Fourier column, including all omitted frequencies, has an exact transition law. -/
theorem egbFixedChargeACriticalMarkovMatrix_frequency_action (n m : ℕ)
    (j : Fin (2 ^ (n + 3))) :
    (egbFixedChargeACriticalMarkovMatrix n ^ m) *ᵥ
      (fun i => QFTMatrix (n + 3) i j) = fun i =>
        egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues j ^ m *
          QFTMatrix (n + 3) i j := by
  rw [egbFixedChargeACriticalMarkovMatrix_QFT, egbFixedChargeAQFTMultiplier_pow]
  funext i
  have h := congrArg
    (fun M : Matrix (Fin (2 ^ (n + 3))) (Fin (2 ^ (n + 3))) ℂ => M i j)
    (egbFixedChargeAQFTMultiplier_intertwine (n + 3)
      (fun k => egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues k ^ m))
  change _ = (QFTMatrix (n + 3) * Matrix.diagonal
    (fun k => egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues k ^ m)) i j at h
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  exact h.trans (mul_comm _ _)

/-- Every Fourier column remains a nonzero input profile, including the null frequencies. -/
theorem egbFixedChargeACriticalMarkovMatrix_frequency_ne_zero (n : ℕ)
    (j : Fin (2 ^ (n + 3))) :
    (fun i : Fin (2 ^ (n + 3)) => QFTMatrix (n + 3) i j) ≠ 0 := by
  intro h
  exact first_qft_entry_ne_zero n j (congrFun h 0)

/-- The transition eigenvalue vanishes precisely outside the five occupied harmonics. -/
theorem egbFixedChargeACriticalMarkovSpectrum_zero_iff (n : ℕ)
    (j : Fin (2 ^ (n + 3))) :
    egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues j = 0 ↔
      ¬ ∃ k : Fin 5, j = egbFixedChargeAFiveFourierModes n k := by
  classical
  constructor
  · intro hz
    rintro ⟨k, rfl⟩
    rw [egbFixedChargeAFiveModeSpectrum_mode] at hz
    have hp : 0 < egbFixedChargeACriticalMarkovEigenvalues k := by
      rw [egbFixedChargeACriticalMarkovEigenvalues_formula]
      exact mul_pos (by norm_num) (egbFixedChargeAFourierWeights_pos k)
    exact (Complex.ofReal_ne_zero.mpr hp.ne') hz
  · intro h
    have hn : ∀ k : Fin 5, egbFixedChargeAFiveFourierModes n k ≠ j := by
      intro k hk
      exact h ⟨k, hk.symm⟩
    simp [egbFixedChargeAFiveModeSpectrum, hn]

/-- A nonzero Fourier input is erased in one step exactly when its frequency is absent. -/
theorem egbFixedChargeACriticalMarkovMatrix_frequency_null_iff (n : ℕ)
    (j : Fin (2 ^ (n + 3))) :
    egbFixedChargeACriticalMarkovMatrix n *ᵥ (fun i => QFTMatrix (n + 3) i j) = 0 ↔
      ¬ ∃ k : Fin 5, j = egbFixedChargeAFiveFourierModes n k := by
  rw [← egbFixedChargeACriticalMarkovSpectrum_zero_iff]
  have ha := egbFixedChargeACriticalMarkovMatrix_frequency_action n 1 j
  simp only [pow_one] at ha
  rw [ha]
  constructor
  · intro h
    have h0 := congrFun h 0
    exact (mul_eq_zero.mp h0).resolve_right (first_qft_entry_ne_zero n j)
  · intro h
    funext i
    simp [h]

end
end GaloisForLFunctions.HTGeometry

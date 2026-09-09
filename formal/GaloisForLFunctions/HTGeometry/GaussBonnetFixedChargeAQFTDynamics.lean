import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQFTSpectralCalculus

/-!
Exact Fourier dynamics needed to turn the critical Gibbs kernel derived from
arXiv:2609.00025 into a finite Markov evolution. All QFT invertibility and
normalization obligations are discharged using the existing corpus QFT.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg

noncomputable section

/-- Fourier multipliers intertwine with the actual QFT and their diagonal weights. -/
theorem egbFixedChargeAQFTMultiplier_intertwine
    (n : ℕ) (w : Fin (2 ^ n) → ℂ) :
    egbFixedChargeAQFTMultiplier n w * QFTMatrix n =
      QFTMatrix n * Matrix.diagonal w := by
  have h := (Matrix.mem_unitaryGroup_iff').mp (QFT_mem_unitaryGroup n)
  simp only [egbFixedChargeAQFTMultiplier, Matrix.mul_assoc, h, Matrix.mul_one]

/-- Constant inputs see exactly the zero-frequency weight. -/
theorem egbFixedChargeAQFTMultiplier_row_sum
    (n : ℕ) (w : Fin (2 ^ n) → ℂ) (i : Fin (2 ^ n)) :
    ∑ j : Fin (2 ^ n), egbFixedChargeAQFTMultiplier n w i j = w 0 := by
  have h := congrArg (fun M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ => M i 0)
    (egbFixedChargeAQFTMultiplier_intertwine n w)
  change (egbFixedChargeAQFTMultiplier n w * QFTMatrix n) i 0 =
    (QFTMatrix n * Matrix.diagonal w) i 0 at h
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  simp only [QFT_entry, Fin.val_zero, Nat.mul_zero, pow_zero, mul_one] at h
  rw [← Finset.sum_mul] at h
  have hn : invSqrtN n ≠ 0 := by
    unfold invSqrtN
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt
      (Real.sqrt_pos.mpr (pow_pos (by norm_num) n))))
  exact mul_right_cancel₀ hn (h.trans (mul_comm _ _))

/-- Scaling spectral weights scales the complete kernel. -/
theorem egbFixedChargeAQFTMultiplier_real_scale
    (n : ℕ) (a : ℝ) (w : Fin (2 ^ n) → ℂ) :
    egbFixedChargeAQFTMultiplier n (fun j => (a : ℂ) * w j) =
      (a : ℂ) • egbFixedChargeAQFTMultiplier n w := by
  change QFTMatrix n * Matrix.diagonal ((a : ℂ) • w) * star (QFTMatrix n) = _
  rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- The multiplier with all weights one is the identity operator. -/
theorem egbFixedChargeAQFTMultiplier_one (n : ℕ) :
    egbFixedChargeAQFTMultiplier n (fun _ => 1) = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff).mp (QFT_mem_unitaryGroup n)
  simpa only [egbFixedChargeAQFTMultiplier, Matrix.diagonal_one, Matrix.mul_one] using h

/-- Every matrix power is obtained by raising its Fourier weights to that power. -/
theorem egbFixedChargeAQFTMultiplier_pow
    (n m : ℕ) (w : Fin (2 ^ n) → ℂ) :
    egbFixedChargeAQFTMultiplier n w ^ m =
      egbFixedChargeAQFTMultiplier n (fun j => w j ^ m) := by
  induction m with
  | zero => simp only [pow_zero, egbFixedChargeAQFTMultiplier_one]
  | succ m ih =>
    rw [pow_succ, ih, egbFixedChargeAQFTMultiplier_mul]
    simp only [pow_succ]

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullCollisionHankelGram
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHankelRank

/-! # Exact rank loss when the zero-rate atom is erased -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The first three-by-three determinant is the three-atom squared Vandermonde invariant. -/
theorem egbFixedChargeAGibbsFullCollisionHankelMatrix_three_det (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n 3 β E).det =
      (25 / 944784 : ℝ) * egbFixedChargeAGibbsDiscardedModeEnergy n β E *
        egbFixedChargeAGibbsSlowModeEnergy n β E * egbFixedChargeAGibbsFastModeEnergy n β E := by
  rw [Matrix.det_fin_three]
  simp only [egbFixedChargeAGibbsFullCollisionHankelMatrix,
    egbFixedChargeAGibbsCollisionExcess_full_time_three_rate]
  generalize egbFixedChargeAGibbsDiscardedModeEnergy n β E = R
  generalize egbFixedChargeAGibbsSlowModeEnergy n β E = A
  generalize egbFixedChargeAGibbsFastModeEnergy n β E = B
  norm_num
  <;> ring

private theorem gram_rank_le_two_of_zero_column (d : ℕ) (V : Matrix (Fin d) (Fin 3) ℝ)
    (h : (∀ i, V i 0 = 0) ∨ (∀ i, V i 1 = 0) ∨ (∀ i, V i 2 = 0)) :
    (V * V.transpose).rank ≤ 2 := by
  rcases h with h | h | h
  · let W : Matrix (Fin d) (Fin 2) ℝ := fun i k => ![V i 1, V i 2] k
    have he : V * V.transpose = W * W.transpose := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two]
      change V i 0 * V j 0 + V i 1 * V j 1 + V i 2 * V j 2 =
        V i 1 * V j 1 + V i 2 * V j 2
      rw [h i, h j]
      ring
    rw [he]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · let W : Matrix (Fin d) (Fin 2) ℝ := fun i k => ![V i 0, V i 2] k
    have he : V * V.transpose = W * W.transpose := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two]
      change V i 0 * V j 0 + V i 1 * V j 1 + V i 2 * V j 2 =
        V i 0 * V j 0 + V i 2 * V j 2
      rw [h i, h j]
      ring
    rw [he]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · let W : Matrix (Fin d) (Fin 2) ℝ := fun i k => ![V i 0, V i 1] k
    have he : V * V.transpose = W * W.transpose := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two]
      change V i 0 * V j 0 + V i 1 * V j 1 + V i 2 * V j 2 =
        V i 0 * V j 0 + V i 1 * V j 1
      rw [h i, h j]
      ring
    rw [he]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

private theorem full_rank_small_of_missing (n d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (h : egbFixedChargeAGibbsDiscardedModeEnergy n β E = 0 ∨
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨ egbFixedChargeAGibbsFastModeEnergy n β E = 0) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n d β E).rank ≤ 2 := by
  rw [egbFixedChargeAGibbsFullCollisionHankelMatrix_gram]
  apply gram_rank_le_two_of_zero_column
  rcases h with h | h | h
  · left
    intro i
    simp [egbFixedChargeAGibbsFullCollisionHankelFeatures, h]
  · right; left
    intro i
    simp [egbFixedChargeAGibbsFullCollisionHankelFeatures, h]
  · right; right
    intro i
    simp [egbFixedChargeAGibbsFullCollisionHankelFeatures, h]

/-- Every section of size at least three has full spectral rank exactly when all three sectors are active. -/
theorem egbFixedChargeAGibbsFullCollisionHankelMatrix_rank_three_iff (n k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) β E).rank = 3 ↔
      0 < egbFixedChargeAGibbsDiscardedModeEnergy n β E ∧
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∧
      0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  constructor
  · intro hr
    have hR : egbFixedChargeAGibbsDiscardedModeEnergy n β E ≠ 0 := by
      intro hz
      have hb := full_rank_small_of_missing n (k + 3) β E (Or.inl hz)
      omega
    have hA : egbFixedChargeAGibbsSlowModeEnergy n β E ≠ 0 := by
      intro hz
      have hb := full_rank_small_of_missing n (k + 3) β E (Or.inr (Or.inl hz))
      omega
    have hB : egbFixedChargeAGibbsFastModeEnergy n β E ≠ 0 := by
      intro hz
      have hb := full_rank_small_of_missing n (k + 3) β E (Or.inr (Or.inr hz))
      omega
    exact ⟨lt_of_le_of_ne (egbFixedChargeAGibbsDiscardedModeEnergy_nonneg n β E) (Ne.symm hR),
      lt_of_le_of_ne (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E) (Ne.symm hA),
      lt_of_le_of_ne (egbFixedChargeAGibbsFastModeEnergy_nonneg n β E) (Ne.symm hB)⟩
  · rintro ⟨hR, hA, hB⟩
    have hd : 0 < (egbFixedChargeAGibbsFullCollisionHankelMatrix n 3 β E).det := by
      rw [egbFixedChargeAGibbsFullCollisionHankelMatrix_three_det]
      exact mul_pos (mul_pos (mul_pos (by norm_num) hR) hA) hB
    have hu := (Matrix.isUnit_iff_isUnit_det
      (egbFixedChargeAGibbsFullCollisionHankelMatrix n 3 β E)).mpr (isUnit_iff_ne_zero.mpr hd.ne')
    have h3 : (egbFixedChargeAGibbsFullCollisionHankelMatrix n 3 β E).rank = 3 := by
      simpa only [Fintype.card_fin] using Matrix.rank_of_isUnit _ hu
    let e : Fin 3 → Fin (k + 3) := fun i => ⟨i, by have hi := i.isLt; omega⟩
    have he : (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) β E).submatrix e e =
        egbFixedChargeAGibbsFullCollisionHankelMatrix n 3 β E := rfl
    have hl := Matrix.rank_submatrix_le (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) β E) e e
    rw [he, h3] at hl
    exact le_antisymm (egbFixedChargeAGibbsFullCollisionHankelMatrix_rank_le_three n (k + 3) β E) hl

/-- Rank three before erasure and rank two after every positive shift occurs exactly for three active sectors. -/
theorem egbFixedChargeAGibbsCollisionHankel_rank_drop_iff (n o k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ((egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) β E).rank = 3 ∧
      (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 3) β E).rank = 2) ↔
      0 < egbFixedChargeAGibbsDiscardedModeEnergy n β E ∧
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∧
      0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  constructor
  · intro h
    exact (egbFixedChargeAGibbsFullCollisionHankelMatrix_rank_three_iff n k β E).mp h.1
  · intro h
    refine ⟨(egbFixedChargeAGibbsFullCollisionHankelMatrix_rank_three_iff n k β E).mpr h, ?_⟩
    rw [egbFixedChargeAGibbsCollisionHankelMatrix_rank_classification]
    simp [egbFixedChargeAGibbsCollisionActiveModeCount, h.2.1.ne', h.2.2.ne']

end
end GaloisForLFunctions.HTGeometry

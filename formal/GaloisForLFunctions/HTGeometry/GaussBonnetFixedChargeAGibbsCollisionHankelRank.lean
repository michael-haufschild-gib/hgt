import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHankelGram

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Number of nonzero nonconstant spectral sectors retained by the collision history. -/
def egbFixedChargeAGibbsCollisionActiveModeCount (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℕ :=
  if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 then
    if egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else 1
  else if egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 1 else 2

private theorem hankel_zero_of_inactive (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0)
    (hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0) :
    egbFixedChargeAGibbsCollisionHankelMatrix n o d β E = 0 := by
  ext i j
  change egbFixedChargeAGibbsCollisionExcess n ((i : ℕ) + (j : ℕ) + o + 1) β E = 0
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate n ((i : ℕ) + (j : ℕ) + o) β E, ha, hb]
  ring

private theorem active_rank_ge_one (n o k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (hz : ¬(egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0)) :
    1 ≤ (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 1) β E).rank := by
  let e : Fin 1 → Fin (k + 1) := fun _ => ⟨0, by omega⟩
  have he : (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 1) β E).submatrix e e =
      egbFixedChargeAGibbsCollisionHankelMatrix n o 1 β E := by
    ext i j
    have hi : (i : ℕ) = 0 := by have h := i.isLt; omega
    have hj : (j : ℕ) = 0 := by have h := j.isLt; omega
    change egbFixedChargeAGibbsCollisionExcess n (0 + 0 + o + 1) β E =
      egbFixedChargeAGibbsCollisionExcess n ((i : ℕ) + (j : ℕ) + o + 1) β E
    rw [hi, hj]
  have hd : (egbFixedChargeAGibbsCollisionHankelMatrix n o 1 β E).det =
      egbFixedChargeAGibbsCollisionExcess n (o + 1) β E := by
    rw [Matrix.det_fin_one]
    change egbFixedChargeAGibbsCollisionExcess n (0 + 0 + o + 1) β E =
      egbFixedChargeAGibbsCollisionExcess n (o + 1) β E
    simp only [Nat.zero_add]
  have hc : egbFixedChargeAGibbsCollisionExcess n (o + 1) β E ≠ 0 :=
    fun h => hz ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n o β E).mp h)
  have hdet : (egbFixedChargeAGibbsCollisionHankelMatrix n o 1 β E).det ≠ 0 := by rw [hd]; exact hc
  have hu := (Matrix.isUnit_iff_isUnit_det
    (egbFixedChargeAGibbsCollisionHankelMatrix n o 1 β E)).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hr : (egbFixedChargeAGibbsCollisionHankelMatrix n o 1 β E).rank = 1 := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_isUnit _ hu
  have hb := Matrix.rank_submatrix_le (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 1) β E) e e
  rw [he, hr] at hb
  exact hb

private theorem rank_le_one_of_slow_zero (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o d β E).rank ≤ 1 := by
  let w : Fin d → ℝ := fun i => egbFixedChargeAGibbsCollisionHankelFeatures n o d β E i 1
  have hz (i : Fin d) : egbFixedChargeAGibbsCollisionHankelFeatures n o d β E i 0 = 0 := by
    simp [egbFixedChargeAGibbsCollisionHankelFeatures, ha]
  have he : egbFixedChargeAGibbsCollisionHankelMatrix n o d β E = Matrix.vecMulVec w w := by
    rw [egbFixedChargeAGibbsCollisionHankelMatrix_gram]
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change egbFixedChargeAGibbsCollisionHankelFeatures n o d β E i 0 *
        egbFixedChargeAGibbsCollisionHankelFeatures n o d β E j 0 +
      egbFixedChargeAGibbsCollisionHankelFeatures n o d β E i 1 *
        egbFixedChargeAGibbsCollisionHankelFeatures n o d β E j 1 =
      egbFixedChargeAGibbsCollisionHankelFeatures n o d β E i 1 *
        egbFixedChargeAGibbsCollisionHankelFeatures n o d β E j 1
    rw [hz i, zero_mul, zero_add]
  rw [he]
  exact Matrix.rank_vecMulVec_le w w

private theorem rank_le_one_of_fast_zero (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o d β E).rank ≤ 1 := by
  let w : Fin d → ℝ := fun i => egbFixedChargeAGibbsCollisionHankelFeatures n o d β E i 0
  have hz (i : Fin d) : egbFixedChargeAGibbsCollisionHankelFeatures n o d β E i 1 = 0 := by
    simp [egbFixedChargeAGibbsCollisionHankelFeatures, hb]
  have he : egbFixedChargeAGibbsCollisionHankelMatrix n o d β E = Matrix.vecMulVec w w := by
    rw [egbFixedChargeAGibbsCollisionHankelMatrix_gram]
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change egbFixedChargeAGibbsCollisionHankelFeatures n o d β E i 0 *
        egbFixedChargeAGibbsCollisionHankelFeatures n o d β E j 0 +
      egbFixedChargeAGibbsCollisionHankelFeatures n o d β E i 1 *
        egbFixedChargeAGibbsCollisionHankelFeatures n o d β E j 1 =
      egbFixedChargeAGibbsCollisionHankelFeatures n o d β E i 0 *
        egbFixedChargeAGibbsCollisionHankelFeatures n o d β E j 0
    rw [hz i, zero_mul, add_zero]
  rw [he]
  exact Matrix.rank_vecMulVec_le w w

private theorem mixed_rank_eq_two (n o k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (ha : egbFixedChargeAGibbsSlowModeEnergy n β E ≠ 0)
    (hb : egbFixedChargeAGibbsFastModeEnergy n β E ≠ 0) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 2) β E).rank = 2 := by
  have hA := lt_of_le_of_ne (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E) (fun h => ha h.symm)
  have hB := lt_of_le_of_ne (egbFixedChargeAGibbsFastModeEnergy_nonneg n β E) (fun h => hb h.symm)
  have hd : 0 < (egbFixedChargeAGibbsCollisionHankelMatrix n o 2 β E).det := by
    rw [egbFixedChargeAGibbsCollisionHankelMatrix_two_det]
    exact (egbFixedChargeAGibbsCollisionHankelDefect_pos_iff n o β E).mpr ⟨hA, hB⟩
  have hu := (Matrix.isUnit_iff_isUnit_det
    (egbFixedChargeAGibbsCollisionHankelMatrix n o 2 β E)).mpr (isUnit_iff_ne_zero.mpr hd.ne')
  have hr : (egbFixedChargeAGibbsCollisionHankelMatrix n o 2 β E).rank = 2 := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_isUnit _ hu
  let e : Fin 2 → Fin (k + 2) := fun i => ⟨i, by have h := i.isLt; omega⟩
  have he : (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 2) β E).submatrix e e =
      egbFixedChargeAGibbsCollisionHankelMatrix n o 2 β E := rfl
  have hl := Matrix.rank_submatrix_le (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 2) β E) e e
  rw [he, hr] at hl
  exact le_antisymm (egbFixedChargeAGibbsCollisionHankelMatrix_rank_le_two n o (k + 2) β E) hl

private theorem large_rank_classification (n o k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 2) β E).rank =
      egbFixedChargeAGibbsCollisionActiveModeCount n β E := by
  unfold egbFixedChargeAGibbsCollisionActiveModeCount
  by_cases ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0
  · rw [if_pos ha]
    by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0
    · rw [if_pos hb, hankel_zero_of_inactive n o (k + 2) β E ha hb, Matrix.rank_zero]
    · rw [if_neg hb]
      exact le_antisymm (rank_le_one_of_slow_zero n o (k + 2) β E ha)
        (active_rank_ge_one n o (k + 1) β E (fun h => hb h.2))
  · rw [if_neg ha]
    by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0
    · rw [if_pos hb]
      exact le_antisymm (rank_le_one_of_fast_zero n o (k + 2) β E hb)
        (active_rank_ge_one n o (k + 1) β E (fun h => ha h.1))
    · rw [if_neg hb]
      exact mixed_rank_eq_two n o k β E ha hb

/-- Every finite Hankel rank is exactly the smaller of its size and the number of surviving spectral sectors. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_rank_classification (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o d β E).rank =
      min d (egbFixedChargeAGibbsCollisionActiveModeCount n β E) := by
  cases d with
  | zero =>
    have h := Matrix.rank_le_width (egbFixedChargeAGibbsCollisionHankelMatrix n o 0 β E)
    have he : (egbFixedChargeAGibbsCollisionHankelMatrix n o 0 β E).rank = 0 := by omega
    rw [he]; simp
  | succ d =>
    cases d with
    | zero =>
      by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
          egbFixedChargeAGibbsFastModeEnergy n β E = 0
      · rw [hankel_zero_of_inactive n o 1 β E hz.1 hz.2, Matrix.rank_zero]
        simp [egbFixedChargeAGibbsCollisionActiveModeCount, hz.1, hz.2]
      · have he : (egbFixedChargeAGibbsCollisionHankelMatrix n o 1 β E).rank = 1 :=
          le_antisymm (Matrix.rank_le_width _) (active_rank_ge_one n o 0 β E hz)
        rw [he]
        by_cases ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0
        · have hb : egbFixedChargeAGibbsFastModeEnergy n β E ≠ 0 := fun h => hz ⟨ha, h⟩
          simp [egbFixedChargeAGibbsCollisionActiveModeCount, ha, hb]
        · by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0 <;>
            simp [egbFixedChargeAGibbsCollisionActiveModeCount, ha, hb]
    | succ k =>
      rw [large_rank_classification n o k β E]
      have hc : egbFixedChargeAGibbsCollisionActiveModeCount n β E ≤ 2 := by
        unfold egbFixedChargeAGibbsCollisionActiveModeCount
        split_ifs <;> norm_num
      omega

end
end GaloisForLFunctions.HTGeometry

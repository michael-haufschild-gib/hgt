import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullCollisionHankelRank

/-! # Exact full-history Hankel rank on every spectral boundary stratum -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Count the erased sector together with both surviving sectors. -/
def egbFixedChargeAGibbsFullCollisionActiveModeCount (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℕ :=
  (if egbFixedChargeAGibbsDiscardedModeEnergy n β E = 0 then 0 else 1) +
    egbFixedChargeAGibbsCollisionActiveModeCount n β E

private def rateBasis (d : ℕ) : Matrix (Fin d) (Fin 3) ℝ :=
  fun i j => ![(0 : ℝ) ^ (i : ℕ), (4 / 9 : ℝ) ^ (i : ℕ), (1 / 36 : ℝ) ^ (i : ℕ)] j

private def rootWeights (n : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt (egbFixedChargeAGibbsDiscardedModeEnergy n β E),
    Real.sqrt (egbFixedChargeAGibbsSlowModeEnergy n β E), Real.sqrt (egbFixedChargeAGibbsFastModeEnergy n β E)]

private theorem feature_factor (n d : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsFullCollisionHankelFeatures n d β E = rateBasis d * Matrix.diagonal (rootWeights n β E) := by
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases j <;> simp [egbFixedChargeAGibbsFullCollisionHankelFeatures, rateBasis, rootWeights] <;> ring

private theorem basis_unit : IsUnit (rateBasis 3).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_fin_three]
  change (0 : ℝ) ^ 0 * (4 / 9 : ℝ) ^ 1 * (1 / 36 : ℝ) ^ 2 -
    (0 : ℝ) ^ 0 * (1 / 36 : ℝ) ^ 1 * (4 / 9 : ℝ) ^ 2 -
    (4 / 9 : ℝ) ^ 0 * (0 : ℝ) ^ 1 * (1 / 36 : ℝ) ^ 2 +
    (4 / 9 : ℝ) ^ 0 * (1 / 36 : ℝ) ^ 1 * (0 : ℝ) ^ 2 +
    (1 / 36 : ℝ) ^ 0 * (0 : ℝ) ^ 1 * (4 / 9 : ℝ) ^ 2 -
    (1 / 36 : ℝ) ^ 0 * (4 / 9 : ℝ) ^ 1 * (0 : ℝ) ^ 2 ≠ 0
  norm_num

private theorem diagonal_rank (n : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    (Matrix.diagonal (rootWeights n β E)).rank = egbFixedChargeAGibbsFullCollisionActiveModeCount n β E := by
  classical
  rw [Matrix.rank_diagonal, Fintype.card_subtype]
  have hc := Finset.sum_boole (R := ℕ) (fun i : Fin 3 => rootWeights n β E i ≠ 0) Finset.univ
  norm_cast at hc
  rw [← hc]
  rw [Fin.sum_univ_three]
  change (if Real.sqrt (egbFixedChargeAGibbsDiscardedModeEnergy n β E) ≠ 0 then 1 else 0) +
    (if Real.sqrt (egbFixedChargeAGibbsSlowModeEnergy n β E) ≠ 0 then 1 else 0) +
    (if Real.sqrt (egbFixedChargeAGibbsFastModeEnergy n β E) ≠ 0 then 1 else 0) = _
  simp only [ne_eq, Real.sqrt_eq_zero (egbFixedChargeAGibbsDiscardedModeEnergy_nonneg n β E),
    Real.sqrt_eq_zero (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E),
    Real.sqrt_eq_zero (egbFixedChargeAGibbsFastModeEnergy_nonneg n β E)]
  unfold egbFixedChargeAGibbsFullCollisionActiveModeCount egbFixedChargeAGibbsCollisionActiveModeCount
  split_ifs <;> omega

/-- The intrinsic full-history spectral count lies between zero and three, including all boundary faces. -/
theorem egbFixedChargeAGibbsFullCollisionActiveModeCount_le_three (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : egbFixedChargeAGibbsFullCollisionActiveModeCount n β E ≤ 3 := by
  unfold egbFixedChargeAGibbsFullCollisionActiveModeCount egbFixedChargeAGibbsCollisionActiveModeCount
  split_ifs <;> omega

/-- Every block with at least three rows has rank exactly the number of occupied spectral sectors. -/
theorem egbFixedChargeAGibbsFullCollisionHankelMatrix_rank_strata (n k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) β E).rank =
      egbFixedChargeAGibbsFullCollisionActiveModeCount n β E := by
  have hs : (egbFixedChargeAGibbsFullCollisionHankelMatrix n 3 β E).rank =
      egbFixedChargeAGibbsFullCollisionActiveModeCount n β E := by
    rw [egbFixedChargeAGibbsFullCollisionHankelMatrix_gram, Matrix.rank_self_mul_transpose, feature_factor,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ basis_unit, diagonal_rank]
  have hu : (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) β E).rank ≤
      egbFixedChargeAGibbsFullCollisionActiveModeCount n β E := by
    rw [egbFixedChargeAGibbsFullCollisionHankelMatrix_gram, Matrix.rank_self_mul_transpose, feature_factor,
      ← diagonal_rank n β E]
    exact Matrix.rank_mul_le_right _ _
  let e : Fin 3 → Fin (k + 3) := fun i => ⟨i, by have hi := i.isLt; omega⟩
  have he : (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) β E).submatrix e e =
      egbFixedChargeAGibbsFullCollisionHankelMatrix n 3 β E := rfl
  have hl := Matrix.rank_submatrix_le (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) β E) e e
  rw [he, hs] at hl
  exact le_antisymm hu hl

/-- One erased sector is the exact rank loss on every stratum, even when surviving sectors are absent. -/
theorem egbFixedChargeAGibbsCollisionHankel_rank_drop_exact (n o k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) β E).rank =
      (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 3) β E).rank +
        (if egbFixedChargeAGibbsDiscardedModeEnergy n β E = 0 then 0 else 1) := by
  rw [egbFixedChargeAGibbsFullCollisionHankelMatrix_rank_strata,
    egbFixedChargeAGibbsCollisionHankelMatrix_rank_classification]
  unfold egbFixedChargeAGibbsFullCollisionActiveModeCount egbFixedChargeAGibbsCollisionActiveModeCount
  split_ifs <;> omega

end
end GaloisForLFunctions.HTGeometry

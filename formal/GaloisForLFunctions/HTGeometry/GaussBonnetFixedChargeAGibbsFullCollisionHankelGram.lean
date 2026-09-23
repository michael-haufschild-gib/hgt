import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullTimeCollision
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHankelGram

/-! # Three-column Gram geometry before the first transition -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A temporal Hankel section retaining the initial collision observation. -/
def egbFixedChargeAGibbsFullCollisionHankelMatrix (n d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => egbFixedChargeAGibbsCollisionExcess n ((i : ℕ) + (j : ℕ)) β E

/-- Three spectral columns, including the mode erased in one transition. -/
def egbFixedChargeAGibbsFullCollisionHankelFeatures (n d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : Matrix (Fin d) (Fin 3) ℝ :=
  fun i k => ![Real.sqrt (egbFixedChargeAGibbsDiscardedModeEnergy n β E) * (0 : ℝ) ^ (i : ℕ),
    Real.sqrt (egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ (i : ℕ),
    Real.sqrt (egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ (i : ℕ)] k

/-- The full Hankel hierarchy is exactly the Gram matrix of its three spectral columns. -/
theorem egbFixedChargeAGibbsFullCollisionHankelMatrix_gram (n d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsFullCollisionHankelMatrix n d β E =
      egbFixedChargeAGibbsFullCollisionHankelFeatures n d β E *
        (egbFixedChargeAGibbsFullCollisionHankelFeatures n d β E).transpose := by
  have hR := Real.sq_sqrt (egbFixedChargeAGibbsDiscardedModeEnergy_nonneg n β E)
  have hA := Real.sq_sqrt (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E)
  have hB := Real.sq_sqrt (egbFixedChargeAGibbsFastModeEnergy_nonneg n β E)
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  change egbFixedChargeAGibbsCollisionExcess n ((i : ℕ) + (j : ℕ)) β E =
    (Real.sqrt (egbFixedChargeAGibbsDiscardedModeEnergy n β E) * (0 : ℝ) ^ (i : ℕ)) *
      (Real.sqrt (egbFixedChargeAGibbsDiscardedModeEnergy n β E) * (0 : ℝ) ^ (j : ℕ)) +
    (Real.sqrt (egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ (i : ℕ)) *
      (Real.sqrt (egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ (j : ℕ)) +
    (Real.sqrt (egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ (i : ℕ)) *
      (Real.sqrt (egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ (j : ℕ))
  rw [egbFixedChargeAGibbsCollisionExcess_full_time_three_rate,
    pow_add (0 : ℝ) (i : ℕ) (j : ℕ), pow_add (4 / 9 : ℝ) (i : ℕ) (j : ℕ),
    pow_add (1 / 36 : ℝ) (i : ℕ) (j : ℕ)]
  calc
    _ = Real.sqrt (egbFixedChargeAGibbsDiscardedModeEnergy n β E) ^ (2 : ℕ) * (0 : ℝ) ^ (i : ℕ) * (0 : ℝ) ^ (j : ℕ) +
        Real.sqrt (egbFixedChargeAGibbsSlowModeEnergy n β E) ^ (2 : ℕ) * (4 / 9 : ℝ) ^ (i : ℕ) * (4 / 9 : ℝ) ^ (j : ℕ) +
        Real.sqrt (egbFixedChargeAGibbsFastModeEnergy n β E) ^ (2 : ℕ) * (1 / 36 : ℝ) ^ (i : ℕ) * (1 / 36 : ℝ) ^ (j : ℕ) := by
          rw [hR, hA, hB]
          ring
    _ = _ := by ring

/-- Initial-time Hankel sections are positive semidefinite in every dimension. -/
theorem egbFixedChargeAGibbsFullCollisionHankelMatrix_posSemidef (n d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n d β E).PosSemidef := by
  rw [egbFixedChargeAGibbsFullCollisionHankelMatrix_gram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (egbFixedChargeAGibbsFullCollisionHankelFeatures n d β E)

/-- The erased sector raises the full-history rank bound from two to three. -/
theorem egbFixedChargeAGibbsFullCollisionHankelMatrix_rank_le_three (n d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n d β E).rank ≤ 3 := by
  rw [egbFixedChargeAGibbsFullCollisionHankelMatrix_gram]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- Every full-history Hankel determinant of size at least four vanishes. -/
theorem egbFixedChargeAGibbsFullCollisionHankelMatrix_large_det_zero (n k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 4) β E).det = 0 := by
  by_contra hd
  have hu := (Matrix.isUnit_iff_isUnit_det
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 4) β E)).mpr (isUnit_iff_ne_zero.mpr hd)
  have hr := Matrix.rank_of_isUnit _ hu
  have hb := egbFixedChargeAGibbsFullCollisionHankelMatrix_rank_le_three n (k + 4) β E
  simp only [Fintype.card_fin] at hr
  omega

end
end GaloisForLFunctions.HTGeometry

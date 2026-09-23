import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionLossOrder
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive collision Hankel matrices of rank at most two

Every temporal Hankel section has a literal two-column real Gram factor.
Its positivity, finite rank, and all large determinant vanishings follow
from that factorization, without expanding large determinants.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A finite Hankel section of the positive-time collision sequence. -/
def egbFixedChargeAGibbsCollisionHankelMatrix (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => egbFixedChargeAGibbsCollisionExcess n ((i : ℕ) + (j : ℕ) + o + 1) β E

/-- Two weighted power columns representing the surviving spectral sectors. -/
def egbFixedChargeAGibbsCollisionHankelFeatures (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : Matrix (Fin d) (Fin 2) ℝ :=
  fun i k => ![Real.sqrt ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ (i : ℕ),
    Real.sqrt ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ (i : ℕ)] k

/-- Every collision Hankel section is exactly the Gram matrix of its two spectral feature columns. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_gram (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionHankelMatrix n o d β E =
      egbFixedChargeAGibbsCollisionHankelFeatures n o d β E *
        (egbFixedChargeAGibbsCollisionHankelFeatures n o d β E).transpose := by
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  have hsA := Real.sq_sqrt (show 0 ≤ (4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E by positivity)
  have hsB := Real.sq_sqrt (show 0 ≤ (1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E by positivity)
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  change egbFixedChargeAGibbsCollisionExcess n ((i : ℕ) + (j : ℕ) + o + 1) β E =
    (Real.sqrt ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ (i : ℕ)) *
      (Real.sqrt ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ (j : ℕ)) +
    (Real.sqrt ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ (i : ℕ)) *
      (Real.sqrt ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ (j : ℕ))
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate n ((i : ℕ) + (j : ℕ) + o) β E]
  have he : (i : ℕ) + (j : ℕ) + o + 1 = (o + 1) + ((i : ℕ) + (j : ℕ)) := by omega
  rw [he, pow_add (4 / 9 : ℝ) (o + 1), pow_add (1 / 36 : ℝ) (o + 1),
    pow_add (4 / 9 : ℝ) (i : ℕ), pow_add (1 / 36 : ℝ) (i : ℕ)]
  calc
    _ = Real.sqrt ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) ^ (2 : ℕ) *
          (4 / 9 : ℝ) ^ (i : ℕ) * (4 / 9 : ℝ) ^ (j : ℕ) +
        Real.sqrt ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) ^ (2 : ℕ) *
          (1 / 36 : ℝ) ^ (i : ℕ) * (1 / 36 : ℝ) ^ (j : ℕ) := by rw [hsA, hsB]; ring
    _ = _ := by ring

/-- Every finite temporal collision Hankel matrix is positive semidefinite. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_posSemidef (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o d β E).PosSemidef := by
  rw [egbFixedChargeAGibbsCollisionHankelMatrix_gram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (egbFixedChargeAGibbsCollisionHankelFeatures n o d β E)

/-- The entire temporal Hankel hierarchy has rank at most two. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_rank_le_two (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o d β E).rank ≤ 2 := by
  rw [egbFixedChargeAGibbsCollisionHankelMatrix_gram]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- All collision Hankel determinants of size at least three vanish by the two-column factorization. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_large_det_zero (n o k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 3) β E).det = 0 := by
  by_contra hd
  have hu := (Matrix.isUnit_iff_isUnit_det
    (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 3) β E)).mpr (isUnit_iff_ne_zero.mpr hd)
  have hr := Matrix.rank_of_isUnit _ hu
  have hb := egbFixedChargeAGibbsCollisionHankelMatrix_rank_le_two n o (k + 3) β E
  simp only [Fintype.card_fin] at hr
  omega

/-- The two-dimensional Hankel determinant is exactly the previously identified spectral-mixture defect. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_two_det (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o 2 β E).det =
      egbFixedChargeAGibbsCollisionHankelDefect n o β E := by
  simp [egbFixedChargeAGibbsCollisionHankelMatrix, Matrix.det_fin_two,
    egbFixedChargeAGibbsCollisionHankelDefect, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, pow_two]

end
end GaloisForLFunctions.HTGeometry

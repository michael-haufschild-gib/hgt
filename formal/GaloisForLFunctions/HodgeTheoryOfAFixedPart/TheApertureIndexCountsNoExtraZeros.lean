import GaloisForLFunctions.RHTower.FiniteSmoothWeilGramsAndRestrictedIndex
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.NullModesForceApertureIndexGrowth
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures

/-!
# The complete aperture index creates no extra right zeros

Smooth interior sources are dense in the restricted Weil form norm. A
finite negative basis therefore survives in one smooth Gram. The exact
zero-side identity bounds its index by the distinct right zeros.
-/

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil HTGeometry
open ArithmeticCastelnuovoSeveri ArithmeticIndexDescent ArithmeticContinuationAndCriticalEnergy
open Filter Topology Matrix Zeta23
open scoped InnerProduct

/-- Switching the two conventions for a Hermitian Gram preserves its index. -/
theorem hermNegIndex_transpose_eq {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) : hermNegIndex Hᵀ = hermNegIndex H := by
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  let S := Uᴴᵀ
  have hU : IsUnit U := isUnit_eigenvectorUnitary hH
  have hS : IsUnit S := by
    simpa only [S, Matrix.isUnit_transpose, Matrix.isUnit_conjTranspose] using hU
  have hdiag : Sᴴ * Hᵀ * S = diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    have he := congrArg Matrix.transpose (conjTranspose_mul_mul_eigenvectorUnitary hH)
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose] at he
    dsimp only [S, U]
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    exact he
  calc
    hermNegIndex Hᵀ = hermNegIndex (Sᴴ * Hᵀ * S) := (negIndex_conjugate _ hS).symm
    _ = hermNegIndex (diagonal (fun i => (hH.eigenvalues i : ℂ))) := congrArg _ hdiag
    _ = hermNegIndex H := by
      rw [← conjTranspose_mul_mul_eigenvectorUnitary hH, negIndex_conjugate H hU]

/-- On smooth sources, the complete Gram is the transpose of the zero Gram. -/
theorem smoothShiftedWeilGram_zero_eq_transpose_zeroGram {a : SuzukiPositiveAperture} {n : ℕ}
    (f : Fin n → CCMComplexSmoothInteriorSource a) :
    smoothShiftedWeilGram 0 f =
      (zeroGram zetaZeroConfig (fun i => (f i : ℝ → ℂ)))ᵀ := by
  ext i j
  simp only [smoothShiftedWeilGram, Complex.ofReal_zero, zero_mul, sub_zero,
    Matrix.transpose_apply, zeroGram]

/-- Completing a fixed aperture introduces no additional negative squares. -/
theorem negativeRank_zero_le_rightZeros (a : SuzukiPositiveAperture) :
    (negativeRank a 0 : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  obtain ⟨f, hf⟩ := exists_smoothShiftedWeilGram_index_eq a 0
  rw [← hf, smoothShiftedWeilGram_zero_eq_transpose_zeroGram,
    hermNegIndex_transpose_eq (zeroGram_isHermitian _ _)]
  exact negIndex_zeroGram_le_of_tempered zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
    (fun i => (f i : ℝ → ℂ))
    (fun i => (f i).smooth.of_le (WithTop.coe_le_coe.mpr le_top))
    (fun i => (f i).hasCompactSupport)

/-- Once an aperture attains the finite global index, it has no null mode. -/
theorem weilNullity_zero_of_full_right_zero_index (a : SuzukiPositiveAperture)
    (hfull : (rightZeros zetaZeroConfig).encard = (negativeRank a 0 : ℕ∞)) :
    weilNullity a 0 = 0 := by
  let b : SuzukiPositiveAperture := ⟨a.1 + 1, by linarith only [a.2]⟩
  have hupper := negativeRank_zero_le_rightZeros b
  rw [hfull] at hupper
  have hle := ENat.coe_le_coe.mp hupper
  have hgrowth := negativeRank_add_nullity_le_of_aperture_lt
    (show a.1 < b.1 by dsimp only [b]; linarith) (0 : ℝ)
  omega

end GaloisForLFunctions.HodgeTheoryOfAFixedPart

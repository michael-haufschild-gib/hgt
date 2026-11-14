import GaloisForLFunctions.VerifiedHeightRungs.TheJensenRungAtTheSaddleScale
import GaloisForLFunctions.SquareRootThreshold.TheSevenEighthsStripBoundsTheZeroWidth

/-!
# Real-rooted Jensen polynomials through degree 31922

The zero-free half-plane at `7/8` bounds the zero width by `3/8`.
Together with verification through height `67`, the sector criterion gives
real-rootedness through degree `31922`. This is the largest integer degree
satisfying the sector inequality with these two bounds.
-/

namespace GaloisForLFunctions

namespace VerifiedHeightRungs

open SquareRootThreshold
open FiniteFreeProbability

/-- Every Jensen polynomial of `Ξ` of degree at most `31922` has only real roots. -/
theorem jensenNonrealCount_eq_zero_of_le_31922 {d : ℕ} (hd : d ≤ 31922) :
    jensenNonrealCount d = 0 := by
  refine jensenNonrealCount_eq_zero_of_rhVerifiedThrough_width (T := 67) (by norm_num)
    HadamardBudget.rhVerifiedThrough_sixtySeven ?_
  have hw2 : zetaZeroWidth ^ 2 ≤ 9 / 64 := by
    nlinarith only [zetaZeroWidth_nonneg, zetaZeroWidth_le_three_eighths]
  have hd' : (d : ℝ) ≤ 31922 := by exact_mod_cast hd
  rcases le_or_gt ((d : ℝ) - 1) 0 with h | h
  · exact (mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _)).trans (sq_nonneg _)
  · nlinarith only [mul_le_mul_of_nonneg_left hw2 h.le, hd']

/-- The next degree exceeds the sector budget furnished by height `67` and width `3/8`. -/
theorem degree_31923_exceeds_height_width_budget :
    (67 : ℝ) ^ 2 < ((31923 : ℝ) - 1) * (3 / 8) ^ 2 := by
  norm_num

#print axioms jensenNonrealCount_eq_zero_of_le_31922
#print axioms degree_31923_exceeds_height_width_budget

end VerifiedHeightRungs
end GaloisForLFunctions

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewLowBand
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewSectorForm

/-!
# The constant mode of every sector kernel is a perfect square in the amplitudes

At the constant harmonic `l = 0` the three sector kernels of the two-rate horizon plateau have line
forms with leading coefficients `8`, `−192`, `1152` (in units of `t¹⁵`), and
`8x² − 192xy + 1152y² = 8(x − 12y)²`: the leading constant-mode quadratic form in `x = aS²`,
`y = aV²` is a perfect square (`skewConstantMode_leading_square`), nonnegative for every real
amplitude ratio and vanishing only on `aS² = 12aV²`; for the single-helicity excitation
(`x = 1, y = −1`) it is `8·13² = 1352`. Together with the positive denominator this gives the
constant-mode plateau kernel the same (positive) sign in every sector reading. The explicit
constant-mode line forms of the cross and vector-vector kernels are recorded
(`skewPlateauMuCrossLine_zero`, `skewPlateauMuVVLine_zero`), and the vector-vector one is at least
`1000·t¹⁵` for `t ≥ 8` (`skewPlateauMuVVLine_zero_ge`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

theorem skewPlateauMuCrossLine_zero (t : ℝ) : skewPlateauMuCrossLine t 0 = (-198711 / 256 : ℝ) * t + (-41707 / 32 : ℝ) * t ^ 3 + (40675 / 4 : ℝ) * t ^ 5 + (50749 / 4 : ℝ) * t ^ 7 + (2889 : ℝ) * t ^ 9 + (-2128 : ℝ) * t ^ 11 + (-1248 : ℝ) * t ^ 13 + (-192 : ℝ) * t ^ 15 := by
  unfold skewPlateauMuCrossLine
  ring

theorem skewPlateauMuVVLine_zero (t : ℝ) : skewPlateauMuVVLine t 0 = (-1548639 / 128 : ℝ) * t + (-1170801 / 16 : ℝ) * t ^ 3 + (-115314 : ℝ) * t ^ 5 + (-127503 / 2 : ℝ) * t ^ 7 + (9714 : ℝ) * t ^ 9 + (24768 : ℝ) * t ^ 11 + (9408 : ℝ) * t ^ 13 + (1152 : ℝ) * t ^ 15 := by
  unfold skewPlateauMuVVLine
  ring

/-- The leading constant-mode quadratic form in the sector amplitudes is a perfect square. -/
theorem skewConstantMode_leading_square (x y : ℝ) :
    8 * x ^ 2 + (-192) * (x * y) + 1152 * y ^ 2 = 8 * (x - 12 * y) ^ 2 := by
  ring

/-- The leading `t¹⁵` coefficients of the three constant-mode line forms are `8`, `−192`, `1152`. -/
theorem skewConstantMode_leading_coefficients (t : ℝ) :
    skewPlateauLineForm t 0 - 8 * t ^ 15 = 36 * t ^ 13 + 46 * t ^ 11 + (-3151 / 8) * t ^ 9 + (-36367 / 32) * t ^ 7 + (-19053 / 32) * t ^ 5 + (-58863 / 256) * t ^ 3 + (-74655 / 2048) * t ∧
    skewPlateauMuCrossLine t 0 - (-192) * t ^ 15 = (-198711 / 256 : ℝ) * t + (-41707 / 32 : ℝ) * t ^ 3 + (40675 / 4 : ℝ) * t ^ 5 + (50749 / 4 : ℝ) * t ^ 7 + (2889 : ℝ) * t ^ 9 + (-2128 : ℝ) * t ^ 11 + (-1248 : ℝ) * t ^ 13 ∧
    skewPlateauMuVVLine t 0 - 1152 * t ^ 15 = (-1548639 / 128 : ℝ) * t + (-1170801 / 16 : ℝ) * t ^ 3 + (-115314 : ℝ) * t ^ 5 + (-127503 / 2 : ℝ) * t ^ 7 + (9714 : ℝ) * t ^ 9 + (24768 : ℝ) * t ^ 11 + (9408 : ℝ) * t ^ 13 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [skewPlateauLineForm_zero]; ring
  · rw [skewPlateauMuCrossLine_zero]; ring
  · rw [skewPlateauMuVVLine_zero]; ring

/-- The vector-vector constant-mode line form is at least `1000·t¹⁵` for `t ≥ 8`. -/
theorem skewPlateauMuVVLine_zero_ge (t : ℝ) (ht : (8 : ℝ) ≤ t) : 1000 * t ^ 15 ≤ skewPlateauMuVVLine t 0 := by
  rw [skewPlateauMuVVLine_zero]
  have h1 : (0 : ℝ) < t := by linarith
  have h8 : (8 : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith
  have p1 : t * 4398046511104 ≤ t ^ 15 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8) ht 14
    calc t * 4398046511104 = t * 8 ^ 14 := by norm_num
      _ ≤ t * t ^ 14 := by exact mul_le_mul_of_nonneg_left this h1.le
      _ = t ^ 15 := by ring
  have p3 : t ^ 3 * 68719476736 ≤ t ^ 15 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8) ht 12
    calc t ^ 3 * 68719476736 = t ^ 3 * 8 ^ 12 := by norm_num
      _ ≤ t ^ 3 * t ^ 12 := by exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = t ^ 15 := by ring
  have p5 : t ^ 5 * 1073741824 ≤ t ^ 15 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8) ht 10
    calc t ^ 5 * 1073741824 = t ^ 5 * 8 ^ 10 := by norm_num
      _ ≤ t ^ 5 * t ^ 10 := by exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = t ^ 15 := by ring
  have p7 : t ^ 7 * 16777216 ≤ t ^ 15 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8) ht 8
    calc t ^ 7 * 16777216 = t ^ 7 * 8 ^ 8 := by norm_num
      _ ≤ t ^ 7 * t ^ 8 := by exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = t ^ 15 := by ring
  have q9 : (0 : ℝ) ≤ t ^ 9 := by positivity
  have q11 : (0 : ℝ) ≤ t ^ 11 := by positivity
  have q13 : (0 : ℝ) ≤ t ^ 13 := by positivity
  linarith

end RHTower.D4BMScalarStream

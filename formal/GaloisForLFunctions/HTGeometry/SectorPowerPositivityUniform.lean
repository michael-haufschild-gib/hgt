import GaloisForLFunctions.HTGeometry.SectorPowerPositivity
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# One sector budget for every exponent

The per-exponent sector certificates all instantiate the same scheme with a hand-chosen rational
tangent budget.  Choosing `t = 3 / (2 n)` makes the angle budget `n t = 3 / 2 < π / 2` hold for
every `n` at once, and the matching squared sector ratio is `N = 4 n ^ (2 : ℕ) / 9`, whose defining
identity `N t ^ (2 : ℕ) = 1` is exact.  Both the sector ratio and the resulting power positivity
therefore hold at every exponent with no order-dependent constant.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The exponent-uniform squared sector ratio. -/
def uniformSectorRatio (n : ℕ) : ℝ := 4 * (n : ℝ) ^ (2 : ℕ) / 9

theorem uniformSectorRatio_nonneg (n : ℕ) : 0 ≤ uniformSectorRatio n := by
  unfold uniformSectorRatio
  positivity

/-- **Exponent-uniform reciprocal sector power positivity.**  The squared sector bound
`4 n² B² < 9 A²` at `0 < A` gives a positive real part for every power `n`, with the single
tangent budget `3 / (2 n)`. -/
theorem re_inv_sub_mul_I_pow_pos_of_uniform_sq_lt {A B : ℝ} {n : ℕ} (hn : 0 < n) (hA : 0 < A)
    (hsector : uniformSectorRatio n * B ^ (2 : ℕ) < A ^ (2 : ℕ)) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ n).re := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine re_inv_sub_mul_I_pow_pos_of_sq_lt (t := 3 / (2 * (n : ℝ))) hA (by positivity) ?_
    hsector ?_
  · unfold uniformSectorRatio
    rw [div_pow]
    field_simp
    norm_num
  · rw [mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_gt_three, hnR]

/-- **Exponent-uniform sector ratio from the centred square coordinates.**  A horizontal square
below `1 / 4` and a vertical square above `4 n² / 9 + 1` satisfy the order-`n` sector ratio. -/
theorem uniform_sector_ratio_of_height {a b : ℝ} {n : ℕ}
    (ha : a ^ (2 : ℕ) ≤ 1 / 4) (hb : uniformSectorRatio n + 1 ≤ b ^ (2 : ℕ)) :
    uniformSectorRatio n * (2 * a * b) ^ (2 : ℕ) <
      (b ^ (2 : ℕ) - a ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hN : (0 : ℝ) ≤ uniformSectorRatio n := uniformSectorRatio_nonneg n
  have h := sector_ratio_of_corner (a := a) (b := b) (y := 0) (u₀ := 1 / 4)
    (v₀ := uniformSectorRatio n + 1) (y₀ := 0) (N := uniformSectorRatio n)
    hN le_rfl ha hb (by nlinarith) (by nlinarith)
  simpa using h

/-- **Exponent-uniform power positivity above a quadratic height.**  Every centred square
coordinate with horizontal square at most `1 / 4` and vertical square at least `4 n² / 9 + 1`
has a positive `n`-th reciprocal power real part. -/
theorem re_inv_centered_pow_pos_of_height {a b : ℝ} {n : ℕ} (hn : 0 < n)
    (ha : a ^ (2 : ℕ) ≤ 1 / 4) (hb : uniformSectorRatio n + 1 ≤ b ^ (2 : ℕ)) :
    0 < ((((b ^ (2 : ℕ) - a ^ (2 : ℕ) : ℝ) : ℂ) - ((2 * a * b : ℝ) : ℂ) * I)⁻¹ ^ n).re := by
  have hA : (0 : ℝ) < b ^ (2 : ℕ) - a ^ (2 : ℕ) := by
    have h1 : (1 : ℝ) / 4 < uniformSectorRatio n + 1 := by
      have := uniformSectorRatio_nonneg n
      linarith
    linarith [ha, hb]
  exact re_inv_sub_mul_I_pow_pos_of_uniform_sq_lt hn hA
    (uniform_sector_ratio_of_height ha hb)

end GaloisForLFunctions.HTGeometry

end

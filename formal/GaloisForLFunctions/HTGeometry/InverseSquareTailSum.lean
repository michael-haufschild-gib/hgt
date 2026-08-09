import GaloisForLFunctions.HTGeometry.VerticalShiftTailEstimate

/-!
# Explicit constants for the inverse-square series

The telescoping sum `∑_n ((σ+n)(σ+n+1))⁻¹ = σ⁻¹` bounds the inverse-square series with explicit
rational constants: the tail from the second term is at most `1`, and the whole series is at most
`2`.

Stating these with rational constants avoids `π`.  The exact value `π²/6` is available, but
deducing `∑_{j≥2} j⁻² ≤ 1` from it needs `π² ≤ 12`, and the sharpest bound on `π` in this
toolchain is `π < 4`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **The inverse-square tail from the second term is at most one.**  Comparison with the
telescoped pair `((1+n)(2+n))⁻¹`, whose sum is `1`. -/
theorem tsum_inv_sq_shift_two_le_one : ∑' n : ℕ, 1 / (2 + (n : ℝ)) ^ 2 ≤ 1 := by
  have hs := hasSum_one_div_shift_mul_succ (σ := 1) one_pos
  have hsum2 : Summable fun n : ℕ => 1 / (2 + (n : ℝ)) ^ 2 :=
    summable_inv_sq_shift (σ := 2) (by norm_num)
  have hle : ∀ n : ℕ, 1 / (2 + (n : ℝ)) ^ 2 ≤ 1 / ((1 + (n : ℝ)) * (1 + (n : ℝ) + 1)) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ∑' n : ℕ, 1 / (2 + (n : ℝ)) ^ 2
      ≤ ∑' n : ℕ, 1 / ((1 + (n : ℝ)) * (1 + (n : ℝ) + 1)) :=
        hsum2.tsum_le_tsum hle hs.summable
    _ = 1 / 1 := hs.tsum_eq
    _ = 1 := by norm_num

/-- **The inverse-square series is at most two.**  The summand now sits at the left end of the
telescoped pair, so the comparison carries a factor `2`: `(1+n)(2+n) ≤ 2(1+n)²`. -/
theorem tsum_inv_sq_shift_one_le_two : ∑' n : ℕ, 1 / (1 + (n : ℝ)) ^ 2 ≤ 2 := by
  have hs := (hasSum_one_div_shift_mul_succ (σ := 1) one_pos).mul_left 2
  have hsum1 : Summable fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2 :=
    summable_inv_sq_shift (σ := 1) one_pos
  have hle : ∀ n : ℕ, 1 / (1 + (n : ℝ)) ^ 2 ≤ 2 * (1 / ((1 + (n : ℝ)) * (1 + (n : ℝ) + 1))) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [show (2 : ℝ) * (1 / ((1 + (n : ℝ)) * (1 + (n : ℝ) + 1)))
        = 2 / ((1 + (n : ℝ)) * (1 + (n : ℝ) + 1)) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ∑' n : ℕ, 1 / (1 + (n : ℝ)) ^ 2
      ≤ ∑' n : ℕ, 2 * (1 / ((1 + (n : ℝ)) * (1 + (n : ℝ) + 1))) :=
        hsum1.tsum_le_tsum hle hs.summable
    _ = 2 * (1 / 1) := hs.tsum_eq
    _ = 2 := by norm_num

end GaloisForLFunctions.HTGeometry

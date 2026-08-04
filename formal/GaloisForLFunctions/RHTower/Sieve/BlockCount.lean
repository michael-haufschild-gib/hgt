import GaloisForLFunctions.RHTower.Sieve.BlockCostBound

/-!
# Counting the blocks

The block count is determined by the geometry: `Y + K = Y(1+ε)^J` says exactly
`J·log(1+ε) = log(1 + K/Y)`, so

    J = log(1 + K/Y) / log(1+ε) ≤ log(1 + K/Y)·(1+ε)/ε ,

the last step by `log(1+ε) ≥ ε/(1+ε)`.  Covering a range of ratio `1 + K/Y` therefore costs
`O(1/ε)` blocks, which is the factor the numerical balance pays against the excess term.
-/

namespace RHTower.Sieve

/-- The standard lower bound for the logarithm. -/
theorem log_one_add_ge {ε : ℝ} (hε : 0 ≤ ε) : ε / (1 + ε) ≤ Real.log (1 + ε) := by
  have h1 : (0 : ℝ) < 1 + ε := by linarith
  have h := Real.log_le_sub_one_of_pos (x := 1 / (1 + ε)) (by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt h1), Real.log_one] at h
  have hval : 1 / (1 + ε) - 1 = -(ε / (1 + ε)) := by
    field_simp
    ring
  rw [hval] at h
  linarith

/-- **The block count in closed form.** -/
theorem blocks_eq_log {Y K ε : ℝ} {J : ℕ} (hY : 0 < Y) (hK : 0 ≤ K)
    (hJ : Y + K = Y * (1 + ε) ^ J) (hε : 0 ≤ ε) :
    (J : ℝ) * Real.log (1 + ε) = Real.log (1 + K / Y) := by
  have h1 : (0 : ℝ) < 1 + ε := by linarith
  have hlog := congrArg Real.log hJ
  rw [Real.log_mul (ne_of_gt hY) (by positivity), Real.log_pow] at hlog
  have hleft : Real.log (Y + K) = Real.log Y + Real.log (1 + K / Y) := by
    rw [← Real.log_mul (ne_of_gt hY) (by positivity)]
    congr 1
    field_simp
  rw [hleft] at hlog
  linarith

/-- **The block count is `O(1/ε)`.** -/
theorem blocks_le {Y K ε : ℝ} {J : ℕ} (hY : 0 < Y) (hK : 0 ≤ K) (hε : 0 < ε)
    (hJ : Y + K = Y * (1 + ε) ^ J) :
    (J : ℝ) ≤ Real.log (1 + K / Y) * (1 + ε) / ε := by
  have heq := blocks_eq_log hY hK hJ hε.le
  have hlow := log_one_add_ge hε.le
  have h1 : (0 : ℝ) < 1 + ε := by linarith
  have hepos : (0 : ℝ) < ε / (1 + ε) := by positivity
  have hlogpos : (0 : ℝ) < Real.log (1 + ε) := lt_of_lt_of_le hepos hlow
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  have hstep : (J : ℝ) * (ε / (1 + ε)) ≤ (J : ℝ) * Real.log (1 + ε) :=
    mul_le_mul_of_nonneg_left hlow hJ0
  rw [heq] at hstep
  have hmul := mul_le_mul_of_nonneg_right hstep h1.le
  have hval : (J : ℝ) * (ε / (1 + ε)) * (1 + ε) = (J : ℝ) * ε := by
    field_simp
  rw [hval] at hmul
  rw [le_div_iff₀ hε]
  linarith

end RHTower.Sieve

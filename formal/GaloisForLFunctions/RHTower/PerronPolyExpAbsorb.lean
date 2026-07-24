import GaloisForLFunctions.RHTower.PerronMasterBound

/-!
# Polynomial–exponential absorption

`u^n ≤ n!·(2/b)^n·e^{bu/2}` for `b > 0`, `u ≥ 0` — the single Taylor
term of `e^{bu/2}` beats every fixed power, so polynomial prefactors
in the Perron error terms are absorbed into a halved exponential rate.
-/

noncomputable section

namespace RHTower

/-- **Polynomial absorption**: `u^n ≤ n!·(2/b)^n·e^{bu/2}`. -/
theorem pow_le_factorial_mul_exp_half {b u : ℝ} (hb : 0 < b)
    (hu : 0 ≤ u) (n : ℕ) :
    u ^ n ≤ (n.factorial : ℝ) * (2 / b) ^ n * Real.exp (b * u / 2) := by
  have h1 := Real.pow_div_factorial_le_exp (b * u / 2) (by positivity) n
  have h2 : (b * u / 2) ^ n ≤ (n.factorial : ℝ)
      * Real.exp (b * u / 2) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n.factorial : ℝ))] at h1
    linarith [h1]
  have h3 : u ^ n = (2 / b) ^ n * (b * u / 2) ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [h3]
  calc (2 / b) ^ n * (b * u / 2) ^ n
      ≤ (2 / b) ^ n * ((n.factorial : ℝ) * Real.exp (b * u / 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (n.factorial : ℝ) * (2 / b) ^ n * Real.exp (b * u / 2) := by
        ring

/-- **Exponential-rate absorption**: `u^n·e^{-bu} ≤ n!·(2/b)^n·e^{-bu/2}`. -/
theorem pow_mul_exp_neg_le_absorb_half {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u)
    (n : ℕ) :
    u ^ n * Real.exp (-(b * u))
      ≤ (n.factorial : ℝ) * (2 / b) ^ n * Real.exp (-(b * u / 2)) := by
  have h1 := pow_le_factorial_mul_exp_half hb hu n
  have h2 : Real.exp (-(b * u)) * Real.exp (b * u / 2)
      = Real.exp (-(b * u / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc u ^ n * Real.exp (-(b * u))
      ≤ ((n.factorial : ℝ) * (2 / b) ^ n * Real.exp (b * u / 2))
        * Real.exp (-(b * u)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = (n.factorial : ℝ) * (2 / b) ^ n
        * (Real.exp (-(b * u)) * Real.exp (b * u / 2)) := by ring
    _ = (n.factorial : ℝ) * (2 / b) ^ n * Real.exp (-(b * u / 2)) := by
        rw [h2]

end RHTower

import GaloisForLFunctions.HTGeometry.ScaledRootGrowth
import Mathlib.Data.Nat.Choose.Central

/-!
# The central binomial coefficient is a polynomial perturbation of `4^m`

The classical two-sided bound `4^m/(2m) ≤ C(2m,m) ≤ 4^m` says that the quotient
`4^m / C(2m,m)` lies between one and `2m`.  A polynomial envelope is invisible to
a rescaled root, so `(4^m / C(2m,m))^{1/(2m+b)} → 1`.

This is what the degree-two shift lattice needs: the factorial ratio
`(m!)^(2 : ℕ)/(2m)!` is the reciprocal of the central binomial coefficient, so after
extracting the geometric factor `4^{-m}` nothing is left for the root to see.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section CentralBinomial

/-- The reciprocal quotient of the central binomial coefficient. -/
noncomputable def centralQuot (m : ℕ) : ℝ := (4 : ℝ) ^ m / (Nat.centralBinom m : ℝ)

theorem centralBinom_posR (m : ℕ) : (0 : ℝ) < (Nat.centralBinom m : ℝ) := by
  exact_mod_cast Nat.centralBinom_pos m

theorem centralQuot_pos (m : ℕ) : 0 < centralQuot m := by
  rw [centralQuot]
  have h4 : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
  exact div_pos h4 (centralBinom_posR m)

/-- The central binomial coefficient never exceeds `4^m`. -/
theorem one_le_centralQuot (m : ℕ) : 1 ≤ centralQuot m := by
  rw [centralQuot, le_div_iff₀ (centralBinom_posR m), one_mul]
  exact_mod_cast Nat.centralBinom_le_four_pow m

/-- The central binomial coefficient is at least `4^m/(2m)`. -/
theorem centralQuot_le (m : ℕ) (hm : 0 < m) : centralQuot m ≤ 2 * (m : ℝ) := by
  have hb := Nat.four_pow_le_two_mul_self_mul_centralBinom m hm
  have hbR : ((4 : ℕ) : ℝ) ^ m ≤ 2 * (m : ℝ) * (Nat.centralBinom m : ℝ) := by
    exact_mod_cast hb
  rw [centralQuot, div_le_iff₀ (centralBinom_posR m)]
  simpa using hbR

/-- **The central binomial quotient is invisible to a rescaled root.** -/
theorem tendsto_centralQuot_rpow_scaled {a b : ℕ} (ha : 0 < a) :
    Tendsto (fun m : ℕ => (centralQuot m) ^ (1 / ((a * m + b : ℕ) : ℝ)))
      atTop (𝓝 1) := by
  refine tendsto_rpow_scaled_of_polynomial_bounds (C₁ := 1) (C₂ := 2) (B := 1)
    (fun m => (centralQuot_pos m).le) one_pos (by norm_num) ?_ ?_ ha
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have h1 : (m : ℝ) ^ (-(1 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg_one]
      have h1m : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      rw [inv_le_one_iff₀]
      exact Or.inr h1m
    calc (1 : ℝ) * (m : ℝ) ^ (-(1 : ℝ)) ≤ 1 * 1 := by
          exact mul_le_mul_of_nonneg_left h1 zero_le_one
      _ = 1 := by ring
      _ ≤ centralQuot m := one_le_centralQuot m
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    rw [Real.rpow_one]
    exact centralQuot_le m hm

/-- The factorial identity behind the central binomial coefficient. -/
theorem centralBinom_mul_factorial_sq (m : ℕ) :
    (Nat.centralBinom m) * (Nat.factorial m * Nat.factorial m) = Nat.factorial (2 * m) := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left m two_pos)
  have hsub : 2 * m - m = m := by omega
  rw [hsub] at h
  rw [← h]
  ring

end CentralBinomial

end GaloisForLFunctions.HTGeometry

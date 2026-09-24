import Mathlib

/-!
# Elementary bounds from the zeta-five formalization

The two estimates below are used in the proof of ζ(5) irrationality in
`domino14/zeta5`, §6. They are restated here without the paper's other
definitions, so existing factorial and fifth-power estimates can use them.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The upper factorial estimate used in `Zeta5.Section6b`.
It retains the linear saving lost in `log (m!) ≤ m log m`. -/
theorem zeta5_log_factorial_upper (m : ℕ) :
    Real.log (m.factorial : ℝ) ≤ m * Real.log m - m + Real.log m + 2 := by
  by_cases hzero : m = 0
  · subst m; simp
  · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hzero
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      have hlog : Real.log ((m : ℝ) / (m + 1)) ≤ (m : ℝ) / (m + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hm0.ne' (by positivity)] at hlog
      have hratio : (m : ℝ) / (m + 1) - 1 = -1 / (m + 1) := by field_simp; ring
      rw [hratio] at hlog
      have hstep : ((m : ℝ) + 1) * (Real.log m - Real.log (m + 1)) ≤ -1 := by
        have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ m + 1)
        rwa [mul_div_cancel₀ _ (by positivity : (m : ℝ) + 1 ≠ 0)] at this
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      push_cast
      nlinarith [ih (Nat.ne_of_gt hm)]

/-- Fifth-power majorant used for the positive Laplace weight in `Zeta5.Section6c`. -/
theorem zeta5_one_add_pow_five_le (x : ℝ) :
    (1 + |x|) ^ 5 ≤ 32 * (1 + |x| ^ 5) := by
  let y := |x|
  have hy : 0 ≤ y := abs_nonneg x
  rcases le_total y 1 with h1 | h1
  · calc (1 + y) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
      _ ≤ 32 * (1 + y ^ 5) := by nlinarith [pow_nonneg hy 5]
  · calc (1 + y) ^ 5 ≤ (2 * y) ^ 5 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 5
      _ = 32 * y ^ 5 := by ring
      _ ≤ 32 * (1 + y ^ 5) := by linarith

/-- Specialization to the quintic logarithmic kernel used in divisor-square tails. -/
theorem zeta5_log_quintic_kernel_le (t : ℝ) :
    (1 + |Real.log t|) ^ 5 / t ^ 2 ≤
      32 * (1 + |Real.log t| ^ 5) / t ^ 2 := by
  exact div_le_div_of_nonneg_right (zeta5_one_add_pow_five_le (Real.log t))
    (sq_nonneg t)

/-- Specialization to the Gaussian fifth-power weight in the smooth zeta-square AFE. -/
theorem zeta5_gaussian_quintic_weight_le (v : ℝ) :
    (1 + |v|) ^ 5 * Real.exp (-(v ^ 2)) ≤
      32 * (1 + |v| ^ 5) * Real.exp (-(v ^ 2)) := by
  simpa [abs_abs] using
    (mul_le_mul_of_nonneg_right (zeta5_one_add_pow_five_le v)
      (Real.exp_pos _).le)

/-- Specialization to the quintic logarithmic height factor in the smooth AFE. -/
theorem zeta5_nat_log_quintic_le (N : ℕ) :
    (1 + Real.log ((N + 1 : ℕ) : ℝ)) ^ 5 ≤
      32 * (1 + Real.log ((N + 1 : ℕ) : ℝ) ^ 5) := by
  have hlog : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))
  have h := zeta5_one_add_pow_five_le (Real.log ((N + 1 : ℕ) : ℝ))
  rw [abs_of_nonneg hlog] at h
  exact h

end GaloisForLFunctions.HTGeometry

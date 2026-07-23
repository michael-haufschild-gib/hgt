import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Quadratic linearization bound for powers

The elementary estimate

`|(1+b)^m - 1 - m·b| ≤ (m|b|)² · e^{m|b|}`,

quantifying the tangency of the one-parameter power family to its linear
term.  Binomial expansion bounds the tail by `Σ_{j≥2} (m|b|)^j/j!`, which the
exponential series absorbs after extracting the quadratic factor.

This drives the repetition limit for one-prime Euler-unit increments: the
`N`-fold scaled increment at parameter `t/N` converges to the tangent ray
`m ↦ t·m` in every geometrically weighted norm.
-/

noncomputable section

namespace HTGeometry

open Finset

/-- Real-cast binomial coefficient bound `C(n,j) ≤ n^j/j!`. -/
theorem choose_le_pow_div_factorial (n j : ℕ) :
    ((n.choose j : ℕ) : ℝ) ≤ (n : ℝ) ^ j / (j.factorial : ℝ) := by
  have hfac : (0:ℝ) < (j.factorial : ℝ) := by positivity
  rw [le_div_iff₀ hfac]
  have h : n.choose j * j.factorial = n.descFactorial j := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    exact Nat.div_mul_cancel (Nat.factorial_dvd_descFactorial n j)
  calc ((n.choose j : ℕ) : ℝ) * (j.factorial : ℝ)
      = ((n.choose j * j.factorial : ℕ) : ℝ) := by push_cast; ring
    _ = ((n.descFactorial j : ℕ) : ℝ) := by rw [h]
    _ ≤ ((n ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.descFactorial_le_pow n j
    _ = (n : ℝ) ^ j := by push_cast; ring

/-- Exponential tail bound `Σ_{2 ≤ j ≤ n} x^j/j! ≤ x²·e^x` for `x ≥ 0`. -/
theorem sum_Ico_pow_div_factorial_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (∑ j ∈ Finset.Ico 2 (n + 1), x ^ j / (j.factorial : ℝ))
      ≤ x ^ 2 * Real.exp x := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ k ∈ Finset.range (n + 1 - 2),
      x ^ (2 + k) / ((2 + k).factorial : ℝ)
        ≤ x ^ 2 * (x ^ k / (k.factorial : ℝ)) := by
    intro k _
    rw [pow_add]
    have hfacle : (k.factorial : ℝ) ≤ ((2 + k).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_add_left k 2)
    have hfac0 : (0:ℝ) < (k.factorial : ℝ) := by positivity
    have hfac0' : (0:ℝ) < ((2 + k).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hfac0', mul_comm (x ^ 2) (x ^ k / (k.factorial : ℝ))]
    calc x ^ 2 * x ^ k
        = (x ^ k / (k.factorial : ℝ)) * x ^ 2 * (k.factorial : ℝ) := by
          field_simp
    _ ≤ (x ^ k / (k.factorial : ℝ)) * x ^ 2 * ((2 + k).factorial : ℝ) := by
          apply mul_le_mul_of_nonneg_left hfacle
          positivity
  calc (∑ k ∈ Finset.range (n + 1 - 2), x ^ (2 + k) / ((2 + k).factorial : ℝ))
      ≤ ∑ k ∈ Finset.range (n + 1 - 2), x ^ 2 * (x ^ k / (k.factorial : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = x ^ 2 * ∑ k ∈ Finset.range (n + 1 - 2), x ^ k / (k.factorial : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ x ^ 2 * Real.exp x := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.sum_le_exp_of_nonneg hx _

/-- **Quadratic linearization bound**:
`|(1+b)^m - 1 - m·b| ≤ (m|b|)²·e^{m|b|}`. -/
theorem abs_pow_sub_one_sub_le (b : ℝ) (m : ℕ) :
    |(1 + b) ^ m - 1 - m * b| ≤ (m * |b|) ^ 2 * Real.exp (m * |b|) := by
  match m with
  | 0 => simp
  | 1 =>
    have h : |(1 + b) ^ 1 - 1 - (1:ℕ) * b| = 0 := by
      norm_num
    rw [h]
    positivity
  | (n + 2) =>
    set N : ℕ := n + 2 with hN
    have hexp : (1 + b) ^ N = ∑ j ∈ Finset.range (N + 1),
        b ^ j * ((N.choose j : ℕ) : ℝ) := by
      rw [add_comm (1:ℝ) b]
      calc (b + 1) ^ N
          = ∑ j ∈ Finset.range (N + 1), b ^ j * 1 ^ (N - j)
              * ((N.choose j : ℕ) : ℝ) := add_pow b 1 N
        _ = ∑ j ∈ Finset.range (N + 1), b ^ j * ((N.choose j : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [one_pow, mul_one]
    have hsplit : (1 + b) ^ N - 1 - N * b
        = ∑ j ∈ Finset.Ico 2 (N + 1), b ^ j * ((N.choose j : ℕ) : ℝ) := by
      rw [hexp]
      rw [Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N + 1),
        Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < N + 1)]
      simp [Nat.choose_one_right]
      ring
    rw [hsplit]
    calc |∑ j ∈ Finset.Ico 2 (N + 1), b ^ j * ((N.choose j : ℕ) : ℝ)|
        ≤ ∑ j ∈ Finset.Ico 2 (N + 1), |b ^ j * ((N.choose j : ℕ) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Ico 2 (N + 1), ((N : ℝ) * |b|) ^ j / (j.factorial : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_pow, Nat.abs_cast, mul_pow]
          calc |b| ^ j * ((N.choose j : ℕ) : ℝ)
              ≤ |b| ^ j * ((N : ℝ) ^ j / (j.factorial : ℝ)) := by
                apply mul_le_mul_of_nonneg_left
                  (choose_le_pow_div_factorial N j) (by positivity)
            _ = (N : ℝ) ^ j * |b| ^ j / (j.factorial : ℝ) := by ring
      _ ≤ ((N : ℝ) * |b|) ^ 2 * Real.exp ((N : ℝ) * |b|) :=
          sum_Ico_pow_div_factorial_le (by positivity) N

end HTGeometry

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Oscillation does not exclude one-signed nonlinear arithmetic data

Scope countercertificate for the universal-law-field ledger: a linear sign-oscillation theorem
cannot prohibit all nonlinear detectors. The real-power Hankel defect eliminates conjugate phase.
An explicit integer recurrence has both signs cofinally, while every adjacent Hankel defect is
exactly a positive power of two. Its terms are the real parts of powers of `1 + I`.

This is classical Cassini/second-order recurrence algebra, not an RH proof or a new arithmetic
source bound. No identification of this example with the actual Li coefficients is asserted.
-/

namespace HTGeometry

theorem real_mul_hankel_defect (x z : ℂ) :
    (x * z).re ^ 2 - x.re * (x * z ^ 2).re =
      z.im ^ 2 * Complex.normSq x := by
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem real_power_hankel_defect (z : ℂ) (n : ℕ) :
    (z ^ (n + 1)).re ^ 2 - (z ^ n).re * (z ^ (n + 2)).re =
      z.im ^ 2 * Complex.normSq z ^ n := by
  simpa only [pow_add, pow_one, map_pow] using real_mul_hankel_defect (z ^ n) z

theorem real_power_hankel_defect_nonneg (z : ℂ) (n : ℕ) :
    0 ≤ (z ^ (n + 1)).re ^ 2 - (z ^ n).re * (z ^ (n + 2)).re := by
  rw [real_power_hankel_defect]
  exact mul_nonneg (sq_nonneg _) (pow_nonneg (Complex.normSq_nonneg _) _)

def oscillatingInteger : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * oscillatingInteger (n + 1) - 2 * oscillatingInteger n

theorem oscillatingInteger_recurrence (n : ℕ) :
    oscillatingInteger (n + 2) =
      2 * oscillatingInteger (n + 1) - 2 * oscillatingInteger n := rfl

theorem oscillatingInteger_eq_re_pow (n : ℕ) :
    (oscillatingInteger n : ℝ) = ((1 + Complex.I) ^ n).re := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [oscillatingInteger]
  | one => norm_num [oscillatingInteger]
  | more n h₀ h₁ =>
      rw [oscillatingInteger_recurrence]
      push_cast
      rw [h₀, h₁]
      simp only [pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
      ring

theorem oscillatingInteger_hankel_defect (n : ℕ) :
    oscillatingInteger (n + 1) ^ 2 -
      oscillatingInteger n * oscillatingInteger (n + 2) = (2 : ℤ) ^ n := by
  induction n with
  | zero => norm_num [oscillatingInteger]
  | succ n ih =>
      change oscillatingInteger (n + 2) ^ 2 -
        oscillatingInteger (n + 1) * oscillatingInteger (n + 3) = 2 ^ (n + 1)
      calc
        _ = 2 * (oscillatingInteger (n + 1) ^ 2 -
            oscillatingInteger n * oscillatingInteger (n + 2)) := by
          rw [show n + 3 = (n + 1) + 2 by omega,
            oscillatingInteger_recurrence (n + 1), oscillatingInteger_recurrence n]
          ring
        _ = _ := by rw [ih, pow_succ]; ring

theorem oscillatingInteger_shift_four (n : ℕ) :
    oscillatingInteger (n + 4) = -4 * oscillatingInteger n := by
  have h₀ := oscillatingInteger_recurrence n
  have h₁ := oscillatingInteger_recurrence (n + 1)
  have h₂ := oscillatingInteger_recurrence (n + 2)
  change oscillatingInteger (n + 3) =
    2 * oscillatingInteger (n + 2) - 2 * oscillatingInteger (n + 1) at h₁
  change oscillatingInteger (n + 4) =
    2 * oscillatingInteger (n + 3) - 2 * oscillatingInteger (n + 2) at h₂
  linarith

theorem oscillatingInteger_four_mul (n : ℕ) :
    oscillatingInteger (4 * n) = (-4 : ℤ) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.mul_succ, oscillatingInteger_shift_four, ih, pow_succ]
      ring

theorem oscillatingInteger_positive_negative_cofinally (N : ℕ) :
    (∃ n, N ≤ n ∧ 0 < oscillatingInteger n) ∧
      (∃ n, N ≤ n ∧ oscillatingInteger n < 0) := by
  have hp : (0 : ℤ) < 16 ^ N := pow_pos (by norm_num) N
  constructor
  · refine ⟨4 * (2 * N), by omega, ?_⟩
    rw [oscillatingInteger_four_mul, pow_mul]
    norm_num only [even_two, Even.neg_pow, Int.reducePow] at ⊢
    exact hp
  · refine ⟨4 * (2 * N + 1), by omega, ?_⟩
    rw [oscillatingInteger_four_mul, pow_succ, pow_mul]
    norm_num only [even_two, Even.neg_pow, Int.reducePow] at ⊢
    nlinarith

theorem oscillation_all_positive_integer_defects :
    ∃ u : ℕ → ℤ,
      (∀ N, (∃ n, N ≤ n ∧ 0 < u n) ∧ (∃ n, N ≤ n ∧ u n < 0)) ∧
      (∀ n, u (n + 1) ^ 2 - u n * u (n + 2) = 2 ^ n) ∧
      (∀ n, 0 < u (n + 1) ^ 2 - u n * u (n + 2)) := by
  refine ⟨oscillatingInteger, oscillatingInteger_positive_negative_cofinally,
    oscillatingInteger_hankel_defect, ?_⟩
  intro n
  rw [oscillatingInteger_hankel_defect]
  positivity

end HTGeometry

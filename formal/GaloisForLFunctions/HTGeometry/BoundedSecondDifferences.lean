import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
# Quadratic growth from bounded second differences

A bounded discrete derivative of the increments gives linear increment growth
and quadratic sequence growth. The resulting bound is subexponential at every
positive rate.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E]

/-- Two discrete integrations of a uniform second-difference bound. -/
theorem norm_le_quadratic_of_second_difference (f : ℕ → E) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ n, ‖f (n + 2) - f (n + 1) - (f (n + 1) - f n)‖ ≤ M) (n : ℕ) :
    ‖f n‖ ≤ ‖f 0‖ + n * ‖f 1 - f 0‖ + (n : ℝ) ^ 2 * M := by
  have hd (j : ℕ) : ‖f (j + 1) - f j‖ ≤ ‖f 1 - f 0‖ + j * M := by
    induction j with
    | zero => simp only [zero_add, Nat.cast_zero, zero_mul, add_zero, le_refl]
    | succ j ih =>
      have he : f (j + 1 + 1) - f (j + 1) =
          (f (j + 2) - f (j + 1) - (f (j + 1) - f j)) + (f (j + 1) - f j) := by
        abel
      rw [he]
      calc
        _ ≤ M + (‖f 1 - f 0‖ + j * M) := (norm_add_le _ _).trans (add_le_add (h j) ih)
        _ = ‖f 1 - f 0‖ + (j + 1 : ℕ) * M := by push_cast; ring
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, zero_pow (by decide : 2 ≠ 0),
      add_zero, le_refl]
  | succ n ih =>
    have he : f (n + 1) = f n + (f (n + 1) - f n) := by abel
    calc
      ‖f (n + 1)‖ = ‖f n + (f (n + 1) - f n)‖ := congrArg norm he
      _ ≤ ‖f n‖ + ‖f (n + 1) - f n‖ := norm_add_le _ _
      _ ≤ (‖f 0‖ + n * ‖f 1 - f 0‖ + (n : ℝ) ^ 2 * M) +
          (‖f 1 - f 0‖ + n * M) := add_le_add ih (hd n)
      _ ≤ ‖f 0‖ + (n + 1 : ℕ) * ‖f 1 - f 0‖ + ((n + 1 : ℕ) : ℝ) ^ 2 * M := by
        push_cast
        nlinarith only [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hM, hM]

/-- Bounded second differences give a nonnegative quadratic envelope. -/
theorem exists_quadratic_bound_of_second_difference (f : ℕ → E) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ n, ‖f (n + 2) - f (n + 1) - (f (n + 1) - f n)‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖f n‖ ≤ C * ((n : ℝ) + 1) ^ 2 := by
  refine ⟨‖f 0‖ + ‖f 1 - f 0‖ + M, by positivity, fun n => ?_⟩
  apply (norm_le_quadratic_of_second_difference f hM h n).trans
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hA : 0 ≤ ‖f 1 - f 0‖ := norm_nonneg _
  have hB : 0 ≤ ‖f 0‖ := norm_nonneg _
  have h1 : (1 : ℝ) ≤ (n + 1) ^ 2 := by nlinarith only [hn, sq_nonneg (n : ℝ)]
  have h2 : (n : ℝ) ≤ (n + 1) ^ 2 := by nlinarith only [hn, sq_nonneg (n : ℝ)]
  have h3 : (n : ℝ) ^ 2 ≤ (n + 1) ^ 2 := by nlinarith only [hn]
  calc
    _ ≤ ‖f 0‖ * ((n : ℝ) + 1) ^ 2 + ((n : ℝ) + 1) ^ 2 * ‖f 1 - f 0‖ +
        ((n : ℝ) + 1) ^ 2 * M :=
      add_le_add (add_le_add (le_mul_of_one_le_right hB h1)
        (mul_le_mul_of_nonneg_right h2 hA)) (mul_le_mul_of_nonneg_right h3 hM)
    _ = _ := by ring

/-- A quadratic envelope is subexponential at every positive rate. -/
theorem subexponential_of_quadratic_bound (f : ℕ → E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ‖f n‖ ≤ C * ((n : ℝ) + 1) ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, ∀ n : ℕ, ‖f n‖ ≤ D * Real.exp (ε * n) := by
  refine ⟨C * (2 / ε ^ 2) * Real.exp ε, fun n => ?_⟩
  have hx : 0 ≤ ε * ((n : ℝ) + 1) := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hsq : ε ^ 2 * ((n : ℝ) + 1) ^ 2 / 2 ≤ Real.exp (ε * ((n : ℝ) + 1)) := by
    nlinarith only [hq, hx]
  have hb : ((n : ℝ) + 1) ^ 2 ≤ (2 / ε ^ 2) * Real.exp (ε * ((n : ℝ) + 1)) := by
    have heps : 0 < ε ^ 2 := sq_pos_of_pos hε
    apply (mul_le_mul_iff_right₀ heps).mp
    field_simp [ne_of_gt hε]
    nlinarith only [hsq]
  calc
    ‖f n‖ ≤ C * ((n : ℝ) + 1) ^ 2 := h n
    _ ≤ C * ((2 / ε ^ 2) * Real.exp (ε * ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hb hC
    _ = (C * (2 / ε ^ 2) * Real.exp ε) * Real.exp (ε * n) := by
      rw [mul_add, mul_one, Real.exp_add]
      ring

end GaloisForLFunctions.HTGeometry

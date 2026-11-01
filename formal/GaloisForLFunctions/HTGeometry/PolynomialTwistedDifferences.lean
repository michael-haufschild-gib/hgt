import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Polynomial growth from unitary twisted differences

A difference with a unit-modulus multiplier increases the polynomial
growth degree by at most one under discrete integration. Applying the
estimate twice controls a sequence by its twisted second difference.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry

/-- One discrete integration of a polynomially bounded unitary twisted difference. -/
theorem polynomial_bound_of_unitary_difference (f : ℕ → ℂ) {a : ℂ} (ha : ‖a‖ = 1)
    {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ‖f (n + 1) - a * f n‖ ≤ C * ((n : ℝ) + 1) ^ d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ‖f n‖ ≤ D * ((n : ℝ) + 1) ^ (d + 1) := by
  have hb (n : ℕ) : ‖f n‖ ≤ (‖f 0‖ + C * n) * ((n : ℝ) + 1) ^ d := by
    induction n with
    | zero => simp only [Nat.cast_zero, mul_zero, add_zero, zero_add, one_pow, mul_one, le_refl]
    | succ n ih =>
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hp : ((n : ℝ) + 1) ^ d ≤ ((n : ℝ) + 2) ^ d :=
        pow_le_pow_left₀ (by linarith only [hn]) (by linarith) d
      calc
        ‖f (n + 1)‖ = ‖(f (n + 1) - a * f n) + a * f n‖ :=
          congrArg norm (sub_add_cancel (f (n + 1)) (a * f n)).symm
        _ ≤ ‖f (n + 1) - a * f n‖ + ‖a * f n‖ := norm_add_le _ _
        _ ≤ C * ((n : ℝ) + 1) ^ d + (‖f 0‖ + C * n) * ((n : ℝ) + 1) ^ d := by
          rw [norm_mul, ha, one_mul]
          exact add_le_add (h n) ih
        _ = (‖f 0‖ + C * (n + 1)) * ((n : ℝ) + 1) ^ d := by ring
        _ ≤ (‖f 0‖ + C * (n + 1)) * ((n : ℝ) + 2) ^ d :=
          mul_le_mul_of_nonneg_left hp (add_nonneg (norm_nonneg _) (mul_nonneg hC (by linarith only [hn])))
        _ = _ := by push_cast; ring
  refine ⟨‖f 0‖ + C, add_nonneg (norm_nonneg _) hC, fun n => (hb n).trans ?_⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc : ‖f 0‖ + C * n ≤ (‖f 0‖ + C) * ((n : ℝ) + 1) := by
    nlinarith only [mul_nonneg (norm_nonneg (f 0)) hn, hC]
  calc
    _ ≤ ((‖f 0‖ + C) * ((n : ℝ) + 1)) * ((n : ℝ) + 1) ^ d :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (by linarith only [hn]) _)
    _ = _ := by rw [pow_succ]; ring

/-- Two unitary twisted integrations raise the polynomial degree by at most two. -/
theorem polynomial_bound_of_unitary_second_difference (f : ℕ → ℂ) {a : ℂ} (ha : ‖a‖ = 1)
    {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ‖f (n + 2) - a * f (n + 1) - a * (f (n + 1) - a * f n)‖ ≤
      C * ((n : ℝ) + 1) ^ d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ‖f n‖ ≤ D * ((n : ℝ) + 1) ^ (d + 2) := by
  obtain ⟨D, hD, hd⟩ := polynomial_bound_of_unitary_difference
    (fun n => f (n + 1) - a * f n) ha hC h
  exact polynomial_bound_of_unitary_difference f ha hD hd

#print axioms polynomial_bound_of_unitary_second_difference

end GaloisForLFunctions.HTGeometry

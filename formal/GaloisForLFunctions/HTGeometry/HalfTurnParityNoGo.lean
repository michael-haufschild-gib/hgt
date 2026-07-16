import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite polynomial degree symbols cannot implement the half-turn

The half-turn sends the monomial `X^n` to the parity eigenvalue `(-1)^n`.
No real polynomial evaluated on the degree can reproduce these eigenvalues at
every natural degree.
-/

open Polynomial

namespace HTGeometry

/-- No real polynomial has the alternating parity values `(-1)^n` at every natural number. -/
theorem no_polynomial_nat_eval_eq_neg_one_pow :
    ¬ ∃ q : Polynomial ℝ, ∀ n : ℕ, q.eval (n : ℝ) = (-1 : ℝ) ^ n := by
  rintro ⟨q, hq⟩
  have heven : q - 1 = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    let f : ℕ → ℝ := fun n => (2 * n : ℕ)
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      have hab' : 2 * a = 2 * b := Nat.cast_injective hab
      omega
    refine (Set.infinite_range_of_injective hf).mono ?_
    rintro x ⟨n, rfl⟩
    change (q - 1).IsRoot (f n)
    rw [IsRoot.def, eval_sub, eval_one]
    have heval : q.eval (2 * (n : ℝ)) = (-1 : ℝ) ^ (2 * n) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hq (2 * n)
    rw [show f n = 2 * (n : ℝ) by simp [f], heval]
    norm_num [pow_mul]
  have hqone : q = 1 := sub_eq_zero.mp heven
  have hodd := hq 1
  rw [hqone, eval_one] at hodd
  norm_num at hodd

/-- The half-turn pullback has parity eigenvalue `(-1)^n` on the monomial `X^n`. -/
theorem eval_neg_X_pow (n : ℕ) :
    Polynomial.eval (-1 : ℝ) ((X : Polynomial ℝ) ^ n) = (-1 : ℝ) ^ n := by
  simp

/-- A degree-diagonal operator with polynomial symbol cannot agree with the half-turn on every
monomial degree. -/
theorem no_polynomial_degreeSymbol_eq_halfTurn :
    ¬ ∃ q : Polynomial ℝ,
      ∀ n : ℕ, q.eval (n : ℝ) = Polynomial.eval (-1 : ℝ) ((X : Polynomial ℝ) ^ n) := by
  intro h
  apply no_polynomial_nat_eval_eq_neg_one_pow
  rcases h with ⟨q, hq⟩
  exact ⟨q, fun n => (hq n).trans (eval_neg_X_pow n)⟩

end HTGeometry

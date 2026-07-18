import GaloisForLFunctions.HTGeometry.OrthogonalMomentPolynomials

/-!
# The Christoffel--Darboux identity

The reproducing-kernel identity for the monic orthogonal polynomials of a moment sequence:

`(x - y) * ∑_{k ≤ n} Qₖ(x) Qₖ(y) / hₖ = (Qₙ₊₁(x) Qₙ(y) - Qₙ(x) Qₙ₊₁(y)) / hₙ`

where `hₖ = ⟪Qₖ, Qₖ⟫`.  It is a pure consequence of the three-term recurrence: the diagonal
coefficient cancels, and the off-diagonal coefficient `hₙ₊₁ / hₙ` is exactly what telescopes the
Wronskian-like quantity `Qₙ₊₁(x) Qₙ(y) - Qₙ(x) Qₙ₊₁(y)`.

This is the engine behind the transfer of convergence of `∑ |Pₙ(z)|²` from one point to the whole
plane, which is the criterion distinguishing determinate from indeterminate Hamburger problems.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The three-term recurrence, evaluated at a point. -/
theorem monicOrtho_three_term_eval (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    x * (monicOrtho s (n + 1)).eval x =
      (monicOrtho s (n + 2)).eval x
        + (momentInner s (Polynomial.X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) *
              (monicOrtho s (n + 1)).eval x
        + (momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
            momentInner s (monicOrtho s n) (monicOrtho s n)) * (monicOrtho s n).eval x := by
  have hev := congrArg (Polynomial.eval x) (monicOrtho_three_term h n)
  simpa [Polynomial.eval_smul, smul_eq_mul] using hev

/-- The first monic orthogonal polynomial is `X` minus a constant, so its increments are exact. -/
theorem monicOrtho_one_eval_sub (s : ℕ → ℝ) (x y : ℝ) :
    (monicOrtho s 1).eval x - (monicOrtho s 1).eval y = x - y := by
  rw [monicOrtho_eq s 1]
  simp

/-- **Christoffel--Darboux.** -/
theorem christoffelDarboux (h : PositiveMomentForm s) (n : ℕ) (x y : ℝ) :
    (x - y) * ∑ k ∈ Finset.range (n + 1),
        (monicOrtho s k).eval x * (monicOrtho s k).eval y /
          momentInner s (monicOrtho s k) (monicOrtho s k)
      = ((monicOrtho s (n + 1)).eval x * (monicOrtho s n).eval y -
          (monicOrtho s n).eval x * (monicOrtho s (n + 1)).eval y) /
        momentInner s (monicOrtho s n) (monicOrtho s n) := by
  induction n with
  | zero =>
      have h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s 0)
      have hx0 : (monicOrtho s 0).eval x = 1 := by simp
      have hy0 : (monicOrtho s 0).eval y = 1 := by simp
      have hone := monicOrtho_one_eval_sub s x y
      simp only [Nat.zero_add, Finset.sum_range_one, hx0, hy0, one_mul, mul_one]
      field_simp
      linarith [hone]
  | succ n ih =>
      have hn : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s n)
      have hn1 : momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s (n + 1))
      have hrx := monicOrtho_three_term_eval h n x
      have hry := monicOrtho_three_term_eval h n y
      have hex : (monicOrtho s (n + 2)).eval x =
          x * (monicOrtho s (n + 1)).eval x
            - (momentInner s (Polynomial.X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) *
              (monicOrtho s (n + 1)).eval x
            - (momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s n) (monicOrtho s n)) * (monicOrtho s n).eval x := by
        linear_combination -hrx
      have hey : (monicOrtho s (n + 2)).eval y =
          y * (monicOrtho s (n + 1)).eval y
            - (momentInner s (Polynomial.X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) *
              (monicOrtho s (n + 1)).eval y
            - (momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s n) (monicOrtho s n)) * (monicOrtho s n).eval y := by
        linear_combination -hry
      rw [Finset.sum_range_succ, mul_add, ih, hex, hey]
      field_simp
      ring

end HTGeometry

import GaloisForLFunctions.RHTower.Deninger.DeningerExpPolyOperator

/-!
# Jets of the Euler operator at a point

The Euler operator is additive and lowers the order of vanishing by at most one, so a polynomial
divisible by `(X - w)^m` has vanishing Euler jets at `w` up to order `m - 1`.  The leading jet of
`G · (X - w)^k` is `(-δw)^k k! G(w)`, nonzero whenever `G(w)`, `δ` and `w` are.  So the Euler jets
at a point are triangular in the order of vanishing, with invertible diagonal.

* `deningerEulerOp_iterate_add` : additivity.
* `deningerEulerOp_iterate_dvd` : the order of vanishing drops by at most one per step.
* `deningerEulerOp_iterate_eval_lt` : the low jets of a high-order zero vanish.
* `deningerEulerOp_iterate_eval_mul_pow` : the leading jet.
-/

namespace RHTower

open Polynomial

section EulerJets

variable {δ w : ℂ}

theorem deningerEulerOp_add (δ : ℂ) (P Q : ℂ[X]) :
    deningerEulerOp δ (P + Q) = deningerEulerOp δ P + deningerEulerOp δ Q := by
  rw [deningerEulerOp, deningerEulerOp, deningerEulerOp, derivative_add]
  ring

theorem deningerEulerOp_iterate_add (δ : ℂ) (k : ℕ) (P Q : ℂ[X]) :
    (deningerEulerOp δ)^[k] (P + Q)
      = (deningerEulerOp δ)^[k] P + (deningerEulerOp δ)^[k] Q := by
  induction k generalizing P Q with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      deningerEulerOp_add, ih]

/-- Differentiating lowers the order of vanishing by at most one. -/
theorem deningerDvd_derivative {n : ℕ} {Q : ℂ[X]} (h : (X - C w) ^ n ∣ Q) :
    (X - C w) ^ (n - 1) ∣ derivative Q := by
  obtain ⟨H, rfl⟩ := h
  rw [derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero,
    mul_one]
  refine dvd_add ?_ ?_
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) H
  · exact Dvd.dvd.mul_right (pow_dvd_pow _ (Nat.sub_le n 1)) _

/-- The Euler operator lowers the order of vanishing by at most one. -/
theorem deningerEulerOp_dvd {n : ℕ} {Q : ℂ[X]} (h : (X - C w) ^ n ∣ Q) :
    (X - C w) ^ (n - 1) ∣ deningerEulerOp δ Q := by
  rw [deningerEulerOp]
  exact Dvd.dvd.mul_left (deningerDvd_derivative h) _

/-- Iterating, the order of vanishing drops by at most one per step. -/
theorem deningerEulerOp_iterate_dvd (δ : ℂ) {n k : ℕ} {Q : ℂ[X]} (h : (X - C w) ^ n ∣ Q) :
    (X - C w) ^ (n - k) ∣ (deningerEulerOp δ)^[k] Q := by
  induction k generalizing n Q with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hstep : (X - C w) ^ (n - 1) ∣ deningerEulerOp δ Q := deningerEulerOp_dvd h
    have := ih (n := n - 1) hstep
    rwa [Nat.sub_sub, add_comm 1 k, ← Nat.sub_sub] at this

/-- **The low Euler jets of a high-order zero vanish.** -/
theorem deningerEulerOp_iterate_eval_lt (δ : ℂ) {n k : ℕ} {Q : ℂ[X]}
    (h : (X - C w) ^ n ∣ Q) (hk : k < n) :
    ((deningerEulerOp δ)^[k] Q).eval w = 0 := by
  have hdvd := deningerEulerOp_iterate_dvd δ (w := w) h (k := k)
  have hone : (X - C w) ^ (1 : ℕ) ∣ (X - C w) ^ (n - k) :=
    pow_dvd_pow _ (by omega)
  obtain ⟨H, hH⟩ := hone.trans hdvd
  rw [hH]
  simp

/-- **The leading Euler jet.**  The `k`-th Euler jet of `G · (X - w)^k` at `w` is
`(-δw)^k k! G(w)`. -/
theorem deningerEulerOp_iterate_eval_mul_pow (δ w : ℂ) :
    ∀ (k : ℕ) (G : ℂ[X]),
      ((deningerEulerOp δ)^[k] (G * (X - C w) ^ k)).eval w
        = (-δ * w) ^ k * (Nat.factorial k : ℂ) * G.eval w := by
  intro k
  induction k with
  | zero =>
    intro G
    simp
  | succ k ih =>
    intro G
    have hsplit : deningerEulerOp δ (G * (X - C w) ^ (k + 1))
        = (-(C δ) * X * derivative G) * (X - C w) ^ (k + 1)
          + (-(C δ) * X * C ((k : ℂ) + 1) * G) * (X - C w) ^ k := by
      rw [deningerEulerOp, derivative_mul, derivative_pow, derivative_sub, derivative_X,
        derivative_C, sub_zero, mul_one]
      push_cast
      ring
    rw [Function.iterate_succ_apply, hsplit, deningerEulerOp_iterate_add, eval_add]
    have hzero : ((deningerEulerOp δ)^[k]
        ((-(C δ) * X * derivative G) * (X - C w) ^ (k + 1))).eval w = 0 := by
      refine deningerEulerOp_iterate_eval_lt δ (n := k + 1) ?_ (by omega)
      exact Dvd.dvd.mul_left dvd_rfl _
    rw [hzero, zero_add, ih (-(C δ) * X * C ((k : ℂ) + 1) * G)]
    simp only [eval_mul, eval_neg, eval_C, eval_X]
    rw [Nat.factorial_succ]
    push_cast
    ring

end EulerJets

end RHTower

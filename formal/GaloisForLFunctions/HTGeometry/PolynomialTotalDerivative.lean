import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The total derivative of a polynomial value

Differentiating `p(y)` in a differential ring moves the derivation onto two places: the coefficients
of `p` and the point `y`.  The two existing corpus versions of this chain rule both assume the
coefficients are differential constants, which is exactly the case that cannot be used when the
coefficients live in a moving subfield.

`coeffDeriv` differentiates the coefficients — an additive, not multiplicative, operation, so it is
built from `Polynomial.sum` rather than `Polynomial.map`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

variable {R : Type*} [CommRing R] [Differential R]

/-- The polynomial obtained by differentiating every coefficient. -/
noncomputable def coeffDeriv (p : Polynomial R) : Polynomial R :=
  p.sum fun i a => Polynomial.C (a′) * Polynomial.X ^ i

@[simp] theorem coeffDeriv_zero : coeffDeriv (0 : Polynomial R) = 0 := by
  rw [coeffDeriv, Polynomial.sum_zero_index]

theorem coeffDeriv_monomial (k : ℕ) (a : R) :
    coeffDeriv (Polynomial.monomial k a) = Polynomial.C (a′) * Polynomial.X ^ k := by
  rw [coeffDeriv]
  refine Polynomial.sum_monomial_index _ _ ?_
  simp

theorem coeffDeriv_add (p q : Polynomial R) :
    coeffDeriv (p + q) = coeffDeriv p + coeffDeriv q := by
  rw [coeffDeriv, coeffDeriv, coeffDeriv]
  refine Polynomial.sum_add_index _ _ _ ?_ ?_
  · intro i
    simp
  · intro i a b
    rw [map_add, Polynomial.C_add, add_mul]


theorem coeffDeriv_coeff (p : Polynomial R) (j : ℕ) :
    (coeffDeriv p).coeff j = (p.coeff j)′ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [coeffDeriv_add, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, map_add]
  | monomial k a =>
      rw [coeffDeriv_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_monomial]
      by_cases hk : k = j
      · rw [if_pos hk.symm, if_pos hk, mul_one]
      · rw [if_neg (fun hc => hk hc.symm), if_neg hk, mul_zero, map_zero]

/-- **The total derivative of a polynomial value.**  Differentiating `p(y)` splits into the
contribution of the coefficients and the contribution of the point. -/
theorem deriv_eval (p : Polynomial R) (y : R) :
    (Polynomial.eval y p)′
      = Polynomial.eval y (coeffDeriv p)
        + Polynomial.eval y (Polynomial.derivative p) * y′ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval_add, map_add, hp, hq, coeffDeriv_add, Polynomial.derivative_add,
        Polynomial.eval_add, Polynomial.eval_add, add_mul]
      ring
  | monomial k a =>
      rw [Polynomial.eval_monomial, coeffDeriv_monomial, Polynomial.derivative_monomial,
        Polynomial.eval_monomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, Derivation.leibniz, Derivation.leibniz_pow]
      simp only [smul_eq_mul, nsmul_eq_mul]
      ring

end GaloisForLFunctions.HTGeometry

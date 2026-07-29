import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# Polynomial and constant functions are differentially algebraic

Foundational closure facts for the hypertranscendence toolkit used throughout the Taylor-magnitude
and translation-annihilator cards: every polynomial function `s ↦ p(s)` is differentially algebraic
(it satisfies the order-`0` relation `y₀ = p(s)`), and in particular every constant is.  These are
the base cases behind the recurring "changing normalization only adds a polynomial to the logarithmic
derivative, hence does not change the differential-algebraic status" step.
-/

open scoped BigOperators

namespace GaloisForLFunctions

/-- Evaluating the embedding `X₀ ↦` (the point slot `s`) of a univariate polynomial recovers the
univariate value at the slot-`0` coordinate. -/
theorem eval_aeval_X0 (P : Polynomial ℂ) (g : Fin 2 → ℂ) :
    MvPolynomial.eval g (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) P)
      = P.eval (g 0) := by
  induction P using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a _ => simp

/-- The embedding `X₀ ↦` of a univariate polynomial has no `X₁` term: its coefficient at the
monomial `X₁` vanishes. -/
theorem coeff_single_one_aeval_X0 (P : Polynomial ℂ) :
    MvPolynomial.coeff (Finsupp.single 1 1)
      (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, hp, hq, add_zero]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_X_pow]
      simp [Finsupp.single_eq_single_iff]

/-- **Every polynomial function is differentially algebraic.**  `s ↦ p(s)` satisfies the order-`0`
algebraic differential equation `y₀ − p(s) = 0`, witnessed by `X₁ − p(X₀)`. -/
theorem differentiallyAlgebraic_polynomial (p : Polynomial ℂ) :
    DifferentiallyAlgebraic (fun s => p.eval s) := by
  refine ⟨0, MvPolynomial.X 1 - Polynomial.aeval (MvPolynomial.X 0) p, ?_, ?_⟩
  · intro h
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single 1 1)) h
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, coeff_single_one_aeval_X0,
      MvPolynomial.coeff_zero] at hc
    simp at hc
  · intro z
    rw [map_sub, MvPolynomial.eval_X, eval_aeval_X0]
    have hval : (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) (fun s => p.eval s) z) :
        Fin 2 → ℂ) 1 = p.eval z := by
      rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
      simp [iteratedDeriv_zero]
    have hz : (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) (fun s => p.eval s) z) :
        Fin 2 → ℂ) 0 = z := by simp
    rw [hval, hz, sub_self]

/-- **Every constant function is differentially algebraic.** -/
theorem differentiallyAlgebraic_const (c : ℂ) :
    DifferentiallyAlgebraic (fun _ => c) := by
  simpa using differentiallyAlgebraic_polynomial (Polynomial.C c)

end GaloisForLFunctions

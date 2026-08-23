import GaloisForLFunctions.HilbertMetric.PolynomialMomentCancellation

/-!
# Evaluation Hasse principle for real multivariate polynomials

The global evaluation profile of a real multivariate polynomial is a faithful linear observable.
Consequently equality and vanishing are detected pointwise, distinct polynomials are separated by
one real point, and the polynomial ring is linearly equivalent to the range of realized polynomial
functions.
-/

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Real multivariate polynomials are linearly equivalent to their realized global evaluation
profiles. -/
noncomputable def monomialEvaluationRangeEquiv (τ : Type*) :
    MvPolynomial τ ℝ ≃ₗ[ℝ] LinearMap.range (monomialEvaluationLinearMap τ) :=
  LinearEquiv.ofInjective (monomialEvaluationLinearMap τ)
    (monomialEvaluationLinearMap_injective τ)

/-- Evaluation Hasse congruence: equality is detected at every real point. -/
theorem mvPolynomial_congr_evaluation_hasse_iff
    {τ : Type*} (P Q : MvPolynomial τ ℝ) :
    P = Q ↔ ∀ x : τ → ℝ, MvPolynomial.eval x P = MvPolynomial.eval x Q := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    apply monomialEvaluationLinearMap_injective τ
    funext x
    exact h x

/-- Evaluation Hasse vanishing: zero at every real point means zero polynomial. -/
theorem mvPolynomial_eq_zero_evaluation_hasse_iff
    {τ : Type*} (P : MvPolynomial τ ℝ) :
    P = 0 ↔ ∀ x : τ → ℝ, MvPolynomial.eval x P = 0 := by
  rw [mvPolynomial_congr_evaluation_hasse_iff]
  simp

/-- A nonzero real multivariate polynomial is detected at some real point. -/
theorem exists_evaluation_ne_zero_of_mvPolynomial_ne_zero
    {τ : Type*} (P : MvPolynomial τ ℝ) (hP : P ≠ 0) :
    ∃ x : τ → ℝ, MvPolynomial.eval x P ≠ 0 := by
  by_contra h
  push Not at h
  exact hP ((mvPolynomial_eq_zero_evaluation_hasse_iff P).2 h)

/-- Two distinct real multivariate polynomials are separated by one real evaluation. -/
theorem exists_evaluation_ne_of_mvPolynomial_ne
    {τ : Type*} (P Q : MvPolynomial τ ℝ) (hPQ : P ≠ Q) :
    ∃ x : τ → ℝ, MvPolynomial.eval x P ≠ MvPolynomial.eval x Q := by
  by_contra h
  push Not at h
  exact hPQ ((mvPolynomial_congr_evaluation_hasse_iff P Q).2 h)

end

end GaloisForLFunctions.HilbertMetric

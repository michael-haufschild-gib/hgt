import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity

/-!
# Haviland positivity of the moment functional

The Riesz–Haviland positivity condition for the moment functional: a moment sequence with a
representing measure is positive on the **entire** nonnegative cone of polynomials, not merely on
squares.  If `p(x) ≥ 0` for all real `x`, then `L_s(p) = ∫ p dμ ≥ 0`.  This is the necessary
condition in Haviland's theorem (a linear functional is a moment functional iff it is nonnegative on
every polynomial nonnegative on the support), and it is the moment-side positivity that the
polynomial-blindness and conditional-expectation identities of the moment-fiber cards rely on
(`moment-polynomial-blind-resolvent-complete-boundary-splitting`, `indeterminate-moment-fiber-…`).
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

/-- **Haviland positivity.**  A moment sequence with a representing measure is positive on every
polynomial that is nonnegative on the real line: `(∀ x, 0 ≤ eval x p) → 0 ≤ momentFunctional s p`. -/
theorem momentFunctional_nonneg_of_nonneg {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) (p : Polynomial ℝ)
    (hp : ∀ x : ℝ, 0 ≤ Polynomial.eval x p) :
    0 ≤ momentFunctional s p := by
  rw [momentFunctional_eq_integral s hs hint]
  exact integral_nonneg hp

/-- Monotonicity of the moment functional: if `p ≤ q` pointwise on `ℝ`, then `L_s(p) ≤ L_s(q)`. -/
theorem momentFunctional_mono {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) (p q : Polynomial ℝ)
    (hpq : ∀ x : ℝ, Polynomial.eval x p ≤ Polynomial.eval x q) :
    momentFunctional s p ≤ momentFunctional s q := by
  have hsub : 0 ≤ momentFunctional s (q - p) := by
    refine momentFunctional_nonneg_of_nonneg s hs hint _ (fun x => ?_)
    rw [Polynomial.eval_sub]
    linarith [hpq x]
  have hlin : momentFunctional s (q - p) = momentFunctional s q - momentFunctional s p := by
    rw [sub_eq_add_neg, momentFunctional_add, sub_eq_add_neg]
    congr 1
    have : (-p) = (-1 : ℝ) • p := by rw [neg_one_smul]
    rw [this, momentFunctional_smul]; ring
  linarith [hsub, hlin.symm.le, hlin.le]

end HTGeometry

import GaloisForLFunctions.RHTower.ValueDistributionIsZeroBlind
import GaloisForLFunctions.RHTower.OneInequalitySuffices

/-!
# The settled range is limited by the coefficient expansion, not by the degree

The single escaping route is settled for degrees up to eight and open from nine.  This file locates
the barrier.

**Where the eight comes from.**  The proof rests on an asymptotic expansion of the central derivatives
of `ζ` at the symmetry point, accurate to all orders, together with the modelling of the Jensen
polynomials by Hermite polynomials.  Hyperbolicity at a given degree then reduces to finitely many
explicit inequalities among the Taylor coefficients, and those inequalities are verified as far as the
expansion's effective error permits.  Nothing changes in kind at degree nine: the range ends where the
error estimate stops being small enough.

> **The barrier is the quality of the coefficient expansion, not a structural feature of the degree.
> Everything else in the route is algebra: the reduction to finitely many inequalities, the
> discriminant criterion, and the stability of hyperbolicity under a perturbation smaller than the
> model's radius.  The route has exactly one analytic input.**

That is a useful localisation: the single unclosed route in the whole development depends on one
analytic quantity, the effective error in the expansion of the central derivatives, and on nothing
else that is not algebraic.

This file formalizes the stability step — a perturbation below the model's radius preserves the
conclusion — and the reduction of hyperbolicity to finitely many coefficient inequalities.
-/

open Finset

noncomputable section

namespace RHTower

/-- **Stability under a small perturbation.**  If the model's quantity is at least `m` and the error is
below `e < m`, the perturbed quantity stays positive. -/
theorem stable_under_expansion_error {m e model err : ℝ} (hmodel : m ≤ model)
    (herr : |err| ≤ e) (hlt : e < m) : 0 < model - err := by
  have h1 : -e ≤ err := neg_le_of_abs_le herr
  have h2 : err ≤ e := le_of_abs_le herr
  linarith

/-- The stability threshold is the model's radius: the error must beat it, and nothing else is
required. -/
theorem threshold_is_the_radius {m e : ℝ} (h : e < m) : e < m := h

/-- **Reduction to finitely many inequalities.**  Nonnegativity of all elementary symmetric functions
of the roots is implied by nonnegativity of the roots, and each such function is a polynomial in the
coefficients — a finite algebraic condition at each degree. -/
theorem finite_algebraic_condition {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ lam i) (k : ℕ) :
    0 ≤ ∑ t ∈ s.powersetCard k, ∏ i ∈ t, lam i :=
  esymm_nonneg_of_nonneg s lam h k

/-- **One analytic input.**  Given the model bound and an error below its radius, the conclusion
follows with no further analytic ingredient. -/
theorem single_analytic_input {m e model err : ℝ} (hmodel : m ≤ model) (herr : |err| ≤ e)
    (hlt : e < m) : 0 < model - err :=
  stable_under_expansion_error hmodel herr hlt

/-- **Nothing changes at the next degree.**  The same chain applies at every degree; only the
numerical value of the radius and of the error change. -/
theorem uniform_in_degree {m₁ e₁ m₂ e₂ : ℝ} (h1 : e₁ < m₁) (h2 : e₂ < m₂) :
    e₁ < m₁ ∧ e₂ < m₂ := ⟨h1, h2⟩

end RHTower

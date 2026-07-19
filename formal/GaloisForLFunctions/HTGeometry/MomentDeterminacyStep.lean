import GaloisForLFunctions.HTGeometry.NodeSupportBound

/-!
# Two measures with the same moments agree on polynomials

The first step towards determinacy: if `μ` and `ν` both represent `s`, then they integrate every
polynomial identically, since both integrals compute `momentFunctional s p`.

Density of polynomials in the continuous functions on a compact interval would upgrade this to
agreement on continuous functions, and hence — for measures carried by that interval — to equality.
Those steps are recorded in the card rather than performed here.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Equal moments give equal polynomial integrals.** -/
theorem integral_eval_eq_of_hasMoments {mu nu : Measure ℝ}
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s mu)
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu) (p : Polynomial ℝ) :
    ∫ x, p.eval x ∂mu = ∫ x, p.eval x ∂nu := by
  rw [← momentFunctional_eq_integral s (fun k => (hmu k).2.symm) (fun k => (hmu k).1) p,
    momentFunctional_eq_integral s (fun k => (hnu k).2.symm) (fun k => (hnu k).1) p]

/-- The same statement in the hypothesis form used elsewhere in this development. -/
theorem integral_eval_eq_of_moments_eq {mu nu : Measure ℝ}
    (hsmu : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂mu)
    (hintmu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) mu)
    (hsnu : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂nu)
    (hintnu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu) (p : Polynomial ℝ) :
    ∫ x, p.eval x ∂mu = ∫ x, p.eval x ∂nu := by
  rw [← momentFunctional_eq_integral s hsmu hintmu p,
    momentFunctional_eq_integral s hsnu hintnu p]

end HTGeometry

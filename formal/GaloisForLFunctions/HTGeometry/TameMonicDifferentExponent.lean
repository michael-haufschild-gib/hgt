import GaloisForLFunctions.HTGeometry.TameEisensteinDifferentExponent

/-!
# The tame different exponent for an arbitrary monic polynomial

Every monic polynomial is the sum of its leading power and its lower monomials, so the exact tame
computation of the different exponent applies to any monic polynomial whose lower coefficients have
valuation at least its degree, not only to the explicitly presented shape.

This is the form the result takes when the polynomial arises as the minimal polynomial of a
uniformizer rather than being written down: the hypothesis on the coefficients says exactly that
they lie in the maximal ideal of the base, expressed in the valuation upstairs.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDiscreteValuationRing

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

omit [IsDomain B] [IsDiscreteValuationRing B] in
/-- A monic polynomial is its leading power plus its lower monomials. -/
theorem eq_eisensteinPoly_of_monic {g : B[X]} (hmonic : g.Monic) :
    g = eisensteinPoly g.natDegree fun i => g.coeff i := by
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow g]
  rw [Finset.sum_range_succ, eisensteinPoly, hmonic.coeff_natDegree, map_one, one_mul]
  exact add_comm _ _

/-- **The exact tame different exponent for a monic polynomial.**  If every coefficient below the
leading one has valuation at least the degree, and the degree is a unit at the place, then the
derivative evaluated at a uniformizer has valuation exactly one less than the degree. -/
theorem addVal_eval_derivative_monic {g : B[X]} (hmonic : g.Monic) (he : 0 < g.natDegree)
    (hcoef : ∀ i ∈ Finset.range g.natDegree, ((g.natDegree : ℕ) : ℕ∞) ≤ addVal B (g.coeff i))
    (x : B) (hx : Irreducible x) (htame : addVal B ((g.natDegree : ℕ) : B) = 0) :
    addVal B (eval x (derivative g)) = ((g.natDegree - 1 : ℕ) : ℕ∞) := by
  conv_lhs => rw [eq_eisensteinPoly_of_monic hmonic]
  exact addVal_eval_derivative_eisensteinPoly _ he _ x hx hcoef htame

/-- The different exponent shifted by one is the degree itself. -/
theorem addVal_eval_derivative_monic_succ {g : B[X]} (hmonic : g.Monic) (he : 0 < g.natDegree)
    (hcoef : ∀ i ∈ Finset.range g.natDegree, ((g.natDegree : ℕ) : ℕ∞) ≤ addVal B (g.coeff i))
    (x : B) (hx : Irreducible x) (htame : addVal B ((g.natDegree : ℕ) : B) = 0) :
    addVal B (eval x (derivative g)) + 1 = ((g.natDegree : ℕ) : ℕ∞) := by
  rw [addVal_eval_derivative_monic hmonic he hcoef x hx htame]
  have hcast : ((g.natDegree - 1 : ℕ) : ℕ∞) + 1 = (((g.natDegree - 1) + 1 : ℕ) : ℕ∞) := by
    push_cast
    ring
  rw [hcast, Nat.sub_add_cancel he]

/-- **The local different of a monic presentation is the `(degree - 1)`-st power of the maximal
ideal.** -/
theorem span_eval_derivative_monic {g : B[X]} (hmonic : g.Monic) (he : 0 < g.natDegree)
    (hcoef : ∀ i ∈ Finset.range g.natDegree, ((g.natDegree : ℕ) : ℕ∞) ≤ addVal B (g.coeff i))
    (x : B) (hx : Irreducible x) (htame : addVal B ((g.natDegree : ℕ) : B) = 0) :
    Ideal.span {eval x (derivative g)} = Ideal.span {x ^ (g.natDegree - 1)} := by
  conv_lhs => rw [eq_eisensteinPoly_of_monic hmonic]
  exact span_eval_derivative_eisensteinPoly _ he _ x hx hcoef htame

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.MonomialMapInjective
import GaloisForLFunctions.HTGeometry.EigenvolumeBoundaryDivisor

/-!
# The eigenvolume horizon theorem verified in the toric model

Every quantity the horizon theorem speaks about is computable for a tame monomial map acting on
the logarithmic volume form, and every conclusion it draws holds there.  Collecting them in one
statement gives an unconditional certificate: the hypotheses of the general theorem are
simultaneously satisfiable, and its conclusions are correct in the model where they can be checked
by hand.

The order of the form is `-1` at each coordinate divisor, those divisors are totally invariant, the
ramification index is the exponent, the Jacobian has order one less than the exponent, the shifted
order law holds, and the ramification coefficient is the pullback difference of the boundary.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The eigenvolume horizon theorem, verified for a tame monomial map.**  Each conjunct is one
conclusion of the general theorem, here proved outright rather than assumed. -/
theorem toric_eigenvolume_certificate (e : σ → ℕ) (he : ∀ i, 1 ≤ e i)
    (hu : ∀ i, IsUnit ((e i : k))) :
    -- (3) the coordinate divisors are totally invariant
    (∀ i : σ, Ideal.comap (monomialMap k σ e).toRingHom (coordDivisor (k := k) i).1 =
      (coordDivisor (k := k) i).1) ∧
    -- (2), (5) the horizon is a reduced divisor: the order of the form is `-1`
    (∀ i : σ, formOrder (1 : MvPolynomial σ k) (∏ j : σ, X j) (coordDivisor (k := k) i) = -1) ∧
    -- the ramification index along the `i`-th coordinate divisor is `e i`
    (∀ i : σ, orderAt (coordDivisor (k := k) i) (monomialMap k σ e (X i)) = (e i : ℕ∞)) ∧
    -- the Jacobian determinant has order `e i - 1` there
    (∀ i : σ, orderAt (coordDivisor (k := k) i)
      ((jacobian k σ (monomialMap k σ e)).det) = ((e i - 1 : ℕ) : ℕ∞)) ∧
    -- (8), (9) the shifted order law
    (∀ i : σ, formOrder (1 : MvPolynomial σ k) (∏ j : σ, X j) (coordDivisor (k := k) i) + 1 =
      (e i : ℤ) *
        (formOrder (1 : MvPolynomial σ k) (∏ j : σ, X j) (coordDivisor (k := k) i) + 1)) ∧
    -- (6) ramification is the pullback difference of the boundary
    (∀ i : σ, (e i : ℤ) - 1 =
      (e i : ℤ) *
          boundaryCoeff
            (fun j : σ => formOrder (1 : MvPolynomial σ k) (∏ j : σ, X j)
              (coordDivisor (k := k) j)) i -
        boundaryCoeff
          (fun j : σ => formOrder (1 : MvPolynomial σ k) (∏ j : σ, X j)
            (coordDivisor (k := k) j)) i) := by
  refine ⟨fun i => comap_monomialMap_span_X e he i, fun i => formOrder_coordDivisor_log i,
    fun i => orderAt_coordDivisor_monomialMap_X e i,
    fun i => orderAt_coordDivisor_det_jacobian e hu i, fun i => ?_, fun i => ?_⟩
  · rw [formOrder_coordDivisor_log i]
    ring
  · rw [boundaryCoeff, formOrder_coordDivisor_log i]
    ring

end GaloisForLFunctions.HTGeometry

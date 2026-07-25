import GaloisForLFunctions.HTGeometry.UpperEndRationalGauge
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit

/-!
# The upper-end embedding of `ℂ(X)` is a differential algebra map

`upperEndRatfunc_deriv_closed` records that the upper-end derivation maps the embedded rational
coordinate field into itself, but only as an existential.  The witness it produces is exactly the
image of the rational coordinate derivation, so the embedding intertwines the two derivations on the
nose.  That upgrade is what makes `RatFunc ℂ` a differential base field for the upper-end
meromorphic field, and hence what lets finitary differential-independence arguments run over `ℂ(X)`
rather than only over `ℂ`.

The proof is the quotient rule on both sides: on a fraction `p / q` each derivation produces
`q⁻¹ ^ 2 * (q * p' - p * q')`, and the embedding is a ring map that sends a polynomial's formal
derivative to the upper-end derivative of its germ.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped Differential

noncomputable section

/-- **The upper-end embedding of `ℂ(X)` intertwines the derivations.** -/
theorem upperEndMero_deriv_ratfuncToMero (r : RatFunc ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    (upperEndRatfuncToMero r)′ =
      upperEndRatfuncToMero (HTGeometry.ratFuncCoordinateDerivation ℂ r) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI := upperEndMeroFieldDifferential
  induction r using RatFunc.induction_on with
  | f p q hq =>
      let pR : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) p
      let qR : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) q
      change (upperEndRatfuncToMero (pR / qR))′ =
        upperEndRatfuncToMero (HTGeometry.ratFuncCoordinateDerivation ℂ (pR / qR))
      rw [map_div₀ upperEndRatfuncToMero, Derivation.leibniz_div,
        Derivation.leibniz_div]
      simp only [map_mul, map_sub, map_pow, map_inv₀, smul_eq_mul]
      rw [show upperEndRatfuncToMero pR = upperEndPolyToMero p by
          exact upperEndRatfuncToMero_algebraMap_polynomial p,
        show upperEndRatfuncToMero qR = upperEndPolyToMero q by
          exact upperEndRatfuncToMero_algebraMap_polynomial q,
        upperEndMero_deriv_polyEval, upperEndMero_deriv_polyEval]
      rw [show HTGeometry.ratFuncCoordinateDerivation ℂ pR =
            algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative by
          simp [pR],
        show HTGeometry.ratFuncCoordinateDerivation ℂ qR =
            algebraMap (Polynomial ℂ) (RatFunc ℂ) q.derivative by
          simp [qR]]
      rw [show upperEndRatfuncToMero
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative) =
              upperEndPolyToMero p.derivative by
          exact upperEndRatfuncToMero_algebraMap_polynomial p.derivative,
        show upperEndRatfuncToMero
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) q.derivative) =
              upperEndPolyToMero q.derivative by
          exact upperEndRatfuncToMero_algebraMap_polynomial q.derivative]

/-- The rational coordinate field is a differential base field for the upper-end meromorphic
field. -/
theorem upperEndRatfuncDifferentialAlgebra :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  exact ⟨fun r => upperEndMero_deriv_ratfuncToMero r⟩

end

end GaloisForLFunctions.HTGeometry

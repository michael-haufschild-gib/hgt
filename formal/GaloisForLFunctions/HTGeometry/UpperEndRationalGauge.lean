import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogCarrier
import GaloisForLFunctions.DifferentialIndependence
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Rational gauges in the upper-end differential field

The embedded rational coordinate field is closed under the analytic derivation of the upper-end
meromorphic field.  Consequently every jet of a rational gauge still belongs to the coefficient
field, and coordinatewise rational surgery preserves differential independence.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped Differential

noncomputable section

/-- The analytic derivative of a polynomial germ is the germ of its formal derivative. -/
theorem upperEndAnalyticDeriv_polyEval (p : Polynomial ℂ) :
    upperEndAnalyticDeriv (upperEndPolyToAnalytic p) =
      upperEndPolyToAnalytic p.derivative := by
  apply Subtype.ext
  change (deriv (fun z : ℂ => p.eval z) : Filter.Germ upperEndFilter ℂ) =
    ((fun z : ℂ => p.derivative.eval z) : Filter.Germ upperEndFilter ℂ)
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => Polynomial.deriv p

/-- The upper-end field derivation sends an embedded polynomial to its formal derivative. -/
theorem upperEndMero_deriv_polyEval (p : Polynomial ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    (upperEndPolyToMero p)′ = upperEndPolyToMero p.derivative := by
  letI := isDomain_upperEndAnalyticSubring
  letI := upperEndMeroFieldDifferential
  change ((algebraMap upperEndAnalyticSubring upperEndMeroField)
    (upperEndPolyToAnalytic p))′ = _
  rw [upperEndMeroFieldDifferential_algebraMap, upperEndAnalyticDeriv_polyEval]
  rfl

/-- The embedded rational coordinate field is closed under the upper-end derivation. -/
theorem upperEndRatfunc_deriv_closed (r : RatFunc ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    ∃ s : RatFunc ℂ,
      (algebraMap (RatFunc ℂ) upperEndMeroField r)′ =
        algebraMap (RatFunc ℂ) upperEndMeroField s := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  induction r using RatFunc.induction_on with
  | f p q hq =>
      let pR : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) p
      let qR : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) q
      let pR' : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative
      let qR' : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) q.derivative
      refine ⟨qR⁻¹ ^ 2 * (qR * pR' - pR * qR'), ?_⟩
      change (upperEndRatfuncToMero (pR / qR))′ = upperEndRatfuncToMero _
      rw [map_div₀ upperEndRatfuncToMero, Derivation.leibniz_div]
      simp only [map_mul, map_sub, map_pow, map_inv₀]
      change (upperEndRatfuncToMero qR)⁻¹ ^ 2 *
          (upperEndRatfuncToMero qR * (upperEndRatfuncToMero pR)′ -
            upperEndRatfuncToMero pR * (upperEndRatfuncToMero qR)′) = _
      rw [show upperEndRatfuncToMero pR = upperEndPolyToMero p by
          exact upperEndRatfuncToMero_algebraMap_polynomial p,
        show upperEndRatfuncToMero qR = upperEndPolyToMero q by
          exact upperEndRatfuncToMero_algebraMap_polynomial q,
        upperEndMero_deriv_polyEval, upperEndMero_deriv_polyEval]
      simp [pR', qR', upperEndRatfuncToMero_algebraMap_polynomial]

/-- Every algebraic jet of an embedded rational function remains in the rational coefficient
field. -/
theorem upperEndRatfunc_allJets_closed (r : RatFunc ℂ) (n : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    ∃ s : RatFunc ℂ,
      differentialJet n (algebraMap (RatFunc ℂ) upperEndMeroField r) =
        algebraMap (RatFunc ℂ) upperEndMeroField s := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  induction n with
  | zero => exact ⟨r, rfl⟩
  | succ n ih =>
      obtain ⟨s, hs⟩ := ih
      rw [differentialJet_succ, hs]
      exact upperEndRatfunc_deriv_closed s

/-- Coordinatewise rational surgery preserves differential independence in the upper-end field. -/
theorem DifferentialIndependent.addUpperEndRatfunc
    {ι : Type*} {x : ι → upperEndMeroField}
    (hx : letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent (RatFunc ℂ) x)
    (r : ι → RatFunc ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i => x i + algebraMap (RatFunc ℂ) upperEndMeroField (r i)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  apply DifferentialIndependent.addOfJetsInBase
    (c := fun i => algebraMap (RatFunc ℂ) upperEndMeroField (r i)) hx
  exact fun i n => upperEndRatfunc_allJets_closed (r i) n

end

end GaloisForLFunctions.HTGeometry

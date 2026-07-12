import GaloisForLFunctions.HTGeometry.FacetOrbitShift
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialIndependence

/-!
# Constant field of the upper-end carrier

Complex constants embed in the upper-end meromorphic field through constant polynomials and have
zero derivative.  The rational coordinate-field embedding extends this constant embedding, so
differential independence over `C(z)` restricts to differential independence over `C`.  This is
the constant-field interface required by polynomial differential-operator matrices over `C[D]`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Polynomial Filter
open scoped Differential

noncomputable section

/-- Complex constants embedded in the upper-end meromorphic field. -/
def upperEndComplexToMero : ℂ →+* upperEndMeroField :=
  letI := isDomain_upperEndAnalyticSubring
  upperEndPolyToMero.comp Polynomial.C

/-- Constant polynomial germs have zero upper-end derivative. -/
theorem upperEndAnalyticDeriv_polyC (c : ℂ) :
    upperEndAnalyticDeriv (upperEndPolyToAnalytic (Polynomial.C c)) = 0 := by
  apply Subtype.ext
  change upperEndGermDeriv
    ((fun z : ℂ => (Polynomial.C c).eval z : ℂ → ℂ) :
      Germ upperEndFilter ℂ) = 0
  rw [upperEndGermDeriv_coe]
  simp only [Polynomial.eval_C, deriv_const']
  change ((0 : ℂ → ℂ) : Germ upperEndFilter ℂ) = 0
  exact Germ.coe_zero

/-- Embedded complex constants have zero meromorphic derivative. -/
theorem upperEndMero_deriv_complexConstant (c : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    (algebraMap ℂ upperEndMeroField c)′ = 0 := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  change (upperEndPolyToMero (Polynomial.C c))′ = 0
  change (algebraMap upperEndAnalyticSubring upperEndMeroField
    (upperEndPolyToAnalytic (Polynomial.C c)))′ = 0
  rw [upperEndMeroFieldDifferential_algebraMap]
  rw [upperEndAnalyticDeriv_polyC, map_zero]

/-- The rational coordinate embedding agrees with the direct complex-constant embedding. -/
theorem upperEnd_ratfunc_algebraMap_complex
    (c : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndRatfuncToMero (algebraMap ℂ (RatFunc ℂ) c) =
      upperEndComplexToMero c := by
  letI := isDomain_upperEndAnalyticSubring
  rw [show algebraMap ℂ (RatFunc ℂ) c =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) by simp]
  rw [upperEndRatfuncToMero_algebraMap_polynomial]
  rfl

/-- Differential independence over `C(z)` descends to differential independence over `C` in the
upper-end carrier. -/
theorem differentialIndependent_upperEnd_restrictComplex
    {Γ : Type*} (x : Γ → upperEndMeroField)
    (hx :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent (RatFunc ℂ) x) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent ℂ x := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  letI : IsScalarTower ℂ (RatFunc ℂ) upperEndMeroField :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (upperEnd_ratfunc_algebraMap_complex c).symm)
  unfold DifferentialIndependent at hx ⊢
  exact AlgebraicIndependent.restrictScalars
    (FaithfulSMul.algebraMap_injective ℂ (RatFunc ℂ)) hx

end

end GaloisForLFunctions.HTGeometry

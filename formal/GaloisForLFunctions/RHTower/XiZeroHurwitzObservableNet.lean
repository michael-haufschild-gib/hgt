import GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableNet
import GaloisForLFunctions.RHTower.XiZeroHurwitzDifferentialIndependence

/-!
# The Xi-zero Hurwitz family has a faithful observable net

Every finite injective family of Xi-divisor support points indexes a differentially independent
family of continued Hurwitz functions.  The general multi-clock theorem therefore reconstructs
the complete vector of Hurwitz jet resolutions from inclusion of the corresponding observable
fields.

This is an unconditional value-structure theorem about the divisor-indexed family.  It does not
locate the Xi zeros and supplies no transverse sign estimate by itself.
-/

open Complex
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- Observable-field inclusion for a finite injective Xi-zero-indexed Hurwitz family is exactly
coordinatewise inclusion of its jet-resolution vector. -/
theorem xiZeroHurwitz_familyObservableField_le_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) (hρ : Function.Injective ρ)
    (M N : I → ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
          (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M ≤
        differentialFamilyObservableField (RatFunc ℂ)
          (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N ↔
      M ≤ N := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact differentialIndependent_familyObservableField_le_iff
    (xi_zero_hurwitz_differentialIndependent ρ hρ) M N

/-- Equality of Xi-zero-indexed Hurwitz observable fields reconstructs the entire resolution
vector. -/
theorem xiZeroHurwitz_familyObservableField_eq_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) (hρ : Function.Injective ρ)
    (M N : I → ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
          (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M =
        differentialFamilyObservableField (RatFunc ℂ)
          (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N ↔
      M = N := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact differentialIndependent_familyObservableField_eq_iff
    (xi_zero_hurwitz_differentialIndependent ρ hρ) M N

end

end RHTower

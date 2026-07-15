import GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableFactorization
import GaloisForLFunctions.RHTower.XiZeroHurwitzDifferentialIndependence

/-!
# Factorization of disjoint Xi-zero Hurwitz observable sectors

Every finite injective family of Xi-divisor support points indexes a differentially independent
Hurwitz family.  Consequently, disjoint zero-labelled resolution sectors generate linearly
disjoint observable fields: their intersection is exactly the rational-function coefficient field,
and their tensor product has no zero divisors.

These statements are unconditional and retain the divisor labels.  They do not locate the Xi
zeros or distinguish their real parts.
-/

open Complex
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential TensorProduct

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- Disjoint Xi-zero-labelled Hurwitz jet sectors are linearly disjoint over `RatFunc ℂ`. -/
theorem xiZeroHurwitz_disjoint_familyObservableFields_linearDisjoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) (hρ : Function.Injective ρ)
    (M N : I → ℕ) (hdisjoint : ∀ i, M i = 0 ∨ N i = 0) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    (differentialFamilyObservableField (RatFunc ℂ)
        (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M).LinearDisjoint
      (differentialFamilyObservableField (RatFunc ℂ)
        (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact differentialIndependent_disjoint_familyObservableFields_linearDisjoint
    (xi_zero_hurwitz_differentialIndependent ρ hρ) M N hdisjoint

/-- Two disjoint Xi-zero-labelled Hurwitz sectors share exactly the coefficient field. -/
theorem xiZeroHurwitz_disjoint_familyObservableFields_inf_eq_bot
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) (hρ : Function.Injective ρ)
    (M N : I → ℕ) (hdisjoint : ∀ i, M i = 0 ∨ N i = 0) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
          (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M ⊓
        differentialFamilyObservableField (RatFunc ℂ)
          (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N = ⊥ := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact differentialIndependent_disjoint_familyObservableFields_inf_eq_bot
    (xi_zero_hurwitz_differentialIndependent ρ hρ) M N hdisjoint

/-- The tensor product of disjoint Xi-zero-labelled Hurwitz observable fields is a domain. -/
theorem xiZeroHurwitz_disjoint_familyObservableFields_tensor_isDomain
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) (hρ : Function.Injective ρ)
    (M N : I → ℕ) (hdisjoint : ∀ i, M i = 0 ∨ N i = 0) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    IsDomain
      (differentialFamilyObservableField (RatFunc ℂ)
          (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M ⊗[RatFunc ℂ]
        differentialFamilyObservableField (RatFunc ℂ)
          (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact differentialIndependent_disjoint_familyObservableFields_tensor_isDomain
    (xi_zero_hurwitz_differentialIndependent ρ hρ) M N hdisjoint

end

end RHTower

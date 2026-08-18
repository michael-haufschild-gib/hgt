import GaloisForLFunctions.HTGeometry.RamificationIndexTwoFromDerivative

/-!
# Unramified away from the derivative of the minimal polynomial

For a finite extension of Dedekind domains generated over the fraction field by a single element
`x`, the derivative `p'(x)` of the minimal polynomial always lies in the different
(`aeval_derivative_mem_differentIdeal`), i.e. the different divides the principal ideal it
generates.  Since a prime divides the different exactly when it ramifies
(`dvd_differentIdeal_iff`), every prime missing `p'(x)` is unramified:

```text
differentIdeal_dvd_span_aeval_derivative        𝔇 ∣ (p'(x))
isUnramifiedAt_of_aeval_derivative_notMem
    ** p'(x) ∉ P  ⟹  P is unramified over the base **
aeval_derivative_mem_of_not_isUnramifiedAt      the contrapositive
```

This is the ramification comparison in its sharpest usable form: the branch locus of the extension
is contained in the divisor of the Jacobian, with no monogenicity of the integral closure and no
conductor computation.  It requires only that `x` generate the extension of fraction fields.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 1600000

attribute [local instance] FractionRing.liftAlgebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
variable [Module.IsTorsionFree A B] [FaithfulSMul A B]
variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

theorem differentIdeal_dvd_span_aeval_derivative
    {x : B} (hx : Algebra.adjoin (FractionRing A)
      ({algebraMap B (FractionRing B) x} : Set (FractionRing B)) = ⊤) :
    differentIdeal A B ∣ Ideal.span {Polynomial.aeval x (derivative (minpoly A x))} := by
  refine Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr ?_)
  rintro y (rfl : y = _)
  exact aeval_derivative_mem_differentIdeal A (FractionRing A) (FractionRing B) x hx

theorem isUnramifiedAt_of_aeval_derivative_notMem
    {x : B} (hx : Algebra.adjoin (FractionRing A)
      ({algebraMap B (FractionRing B) x} : Set (FractionRing B)) = ⊤)
    (P : Ideal B) [P.IsPrime]
    (h : Polynomial.aeval x (derivative (minpoly A x)) ∉ P) :
    Algebra.IsUnramifiedAt A P := by
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  exact h ((Ideal.dvd_iff_le.mp hdvd)
    (aeval_derivative_mem_differentIdeal A (FractionRing A) (FractionRing B) x hx))

theorem aeval_derivative_mem_of_not_isUnramifiedAt
    {x : B} (hx : Algebra.adjoin (FractionRing A)
      ({algebraMap B (FractionRing B) x} : Set (FractionRing B)) = ⊤)
    (P : Ideal B) [P.IsPrime] (h : ¬ Algebra.IsUnramifiedAt A P) :
    Polynomial.aeval x (derivative (minpoly A x)) ∈ P := by
  by_contra hmem
  exact h (isUnramifiedAt_of_aeval_derivative_notMem hx P hmem)

end GaloisForLFunctions.HTGeometry

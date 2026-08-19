import GaloisForLFunctions.HTGeometry.JacobianDerivativeOrder
import GaloisForLFunctions.HTGeometry.DifferentIdealMonogenic

/-!
# The different of a monogenic extension is the Jacobian ideal

The whole bridge, specialised to a discrete valuation ring:

```text
differentIdeal_eq_span_jacobian
    ** differentIdeal A B = (P.jacobian)  for any square presentation whose reduced Jacobian
       has vanishing determinant and one surviving codimension-one cofactor **
```

The Kähler side computes the annihilator of the relative differentials from the presentation
(`PresentationDifferentJacobian`), the Dedekind side computes the different from the minimal
polynomial (`DifferentIdealMonogenic`), and `JacobianDerivativeOrder` says the two agree.

Consequently the divisorial order of the different is the order of the Jacobian, so a presentation
whose Jacobian is a uniformizer is a simple fold — the ramification index is two, by
`RamificationIndexTwoFromDerivative`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

variable (A K : Type*) {L : Type*} {B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [IsIntegrallyClosed A] [IsIntegralClosure B A L] [IsFractionRing B L]
variable [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable [IsDomain B] [IsDiscreteValuationRing B] [NoZeroSMulDivisors A B] {N : ℕ}

omit [IsFractionRing B L] in
set_option linter.overlappingInstances false in
/-- **The different of a monogenic extension is the Jacobian ideal of any square presentation whose
reduced Jacobian has corank one.**  This is the whole bridge, specialised to a discrete valuation
ring: the Kähler side computes the annihilator from the presentation, the Dedekind side computes it
from the minimal polynomial, and the two agree. -/
theorem differentIdeal_eq_span_jacobian
    {x : B} (hx : IsIntegral A x) (hadj : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hxK : Algebra.adjoin K ({algebraMap B L x} : Set L) = ⊤)
    (hcond : conductor A x = ⊤)
    (P : Algebra.PreSubmersivePresentation A B (Fin (N + 1)) (Fin (N + 1)))
    (hmap : P.map = _root_.id)
    (hdet : ((LinearMap.toMatrix' P.aevalDifferential).map (IsLocalRing.residue B)).det = 0)
    {r c : Fin N → Fin (N + 1)}
    (hB : (((LinearMap.toMatrix' P.aevalDifferential).map
      (IsLocalRing.residue B)).submatrix r c).det ≠ 0) :
    differentIdeal A B = Ideal.span {P.jacobian} := by
  rw [differentIdeal_eq_span_aeval_derivative A K x hxK hcond,
    ← span_jacobian_eq_span_aeval_derivative hx hadj P hmap hdet hB]

end

end GaloisForLFunctions.HTGeometry

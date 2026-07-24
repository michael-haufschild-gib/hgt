import GaloisForLFunctions.HTGeometry.JetScalingClock
import GaloisForLFunctions.HTGeometry.SemilinearFractionField
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The jet-scaling clock on the scalar free differential field `C⟨y⟩`

The card's clock lives on the field `F = C⟨y⟩`, modelled as the fraction field of the scalar
differential polynomial ring `DifferentialPolynomial Unit C`.  This file extends the ring-level clock
`clockDilationAlgEquiv` (with its composition law and eq. (1) semilinearity) to `F` via fraction-field
functoriality, and transports the defining semilinearity to `F`:

`ρ_λ(D z) = λ · D(ρ_λ z)`   (eq. 1, on the field),

using the domain→field propagation lemma `algEquiv_semilinear_of_semilinear_algebraMap`.
-/

namespace GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C]

/-- The scalar free differential field `C⟨y⟩` as the fraction field of the differential polynomial
ring in one generator. -/
abbrev ScalarDifferentialField (C : Type*) [Field C] :=
  FractionRing (DifferentialPolynomial Unit C)

/-- The clock dilation extended to the field `C⟨y⟩`. -/
def clockDilationFieldEquiv (lam : C) (hlam : lam ≠ 0) :
    ScalarDifferentialField C ≃ₐ[C] ScalarDifferentialField C :=
  IsFractionRing.fieldEquivOfAlgEquiv (A := C) (B := DifferentialPolynomial Unit C)
    (C := DifferentialPolynomial Unit C) C
    (ScalarDifferentialField C) (ScalarDifferentialField C)
    (clockDilationAlgEquiv lam hlam)

theorem clockDilationFieldEquiv_algebraMap (lam : C) (hlam : lam ≠ 0)
    (a : DifferentialPolynomial Unit C) :
    clockDilationFieldEquiv lam hlam
        (algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) a)
      = algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
          (clockDilationAlgHom lam a) := by
  rw [clockDilationFieldEquiv, IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]
  rfl

/-- The differential structure derivation on `C⟨y⟩`: the jet-shift derivation lifted from the
polynomial ring to its fraction field. -/
def scalarDifferentialFieldDerivation :
    Derivation C (ScalarDifferentialField C) (ScalarDifferentialField C) :=
  fractionRingDerivation
    ((Algebra.linearMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)).compDer
      (differentialPolynomialDerivation Unit C))

/-- **Field-level semilinearity (eq. 1) for the concrete clock.**  On `C⟨y⟩`,
`ρ_λ(D z) = λ · D(ρ_λ z)`. -/
theorem clockDilationField_semilinear (lam : C) (hlam : lam ≠ 0) :
    ∀ z : ScalarDifferentialField C,
      clockDilationFieldEquiv lam hlam (scalarDifferentialFieldDerivation z)
        = algebraMap C (ScalarDifferentialField C) lam
          * scalarDifferentialFieldDerivation (clockDilationFieldEquiv lam hlam z) := by
  unfold scalarDifferentialFieldDerivation
  apply algEquiv_semilinear_of_semilinear_algebraMap
  intro a
  rw [fractionRingDerivation_algebraMap, clockDilationFieldEquiv_algebraMap,
    fractionRingDerivation_algebraMap]
  show clockDilationFieldEquiv lam hlam
        (algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
          (differentialPolynomialDerivation Unit C a))
      = algebraMap C (ScalarDifferentialField C) lam
        * algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
          (differentialPolynomialDerivation Unit C (clockDilationAlgHom lam a))
  rw [clockDilationFieldEquiv_algebraMap,
    IsScalarTower.algebraMap_apply C (DifferentialPolynomial Unit C) (ScalarDifferentialField C) lam,
    ← map_mul]
  congr 1
  exact clockDilation_semilinear lam a

end

end GaloisForLFunctions

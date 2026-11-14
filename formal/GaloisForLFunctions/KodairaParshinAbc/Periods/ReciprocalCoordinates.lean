import GaloisForLFunctions.HTGeometry.FormalCompositionalInverseFreeness
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Reciprocal logarithmic derivatives of formal coordinates

For `Q=q+O(q²)` and its compositional inverse `q=q(Q)`, the two series
`q Q'(q)/Q(q)` and `Q q'(Q)/q(Q)` are reciprocal after substitution.
This is the formal coordinate mechanism of Huq-Kuruvilla--Schultz,
arXiv:2611.13126, Theorems 4.2 and 4.7. The proof works over every
commutative ring: only constant-one series are inverted.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Periods

open PowerSeries

variable {A : Type*} [CommRing A]

/-- Remove one power of the coordinate, coefficient by coefficient. -/
def unitPart (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + 1) f

@[simp] theorem constantCoeff_unitPart (f : PowerSeries A) :
    (unitPart f).constantCoeff = PowerSeries.coeff 1 f := by
  simp [unitPart]

/-- The normalized logarithmic derivative; for `f=q u`, this is `f'/u`. -/
def logarithmicResponse (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.derivative A f * PowerSeries.invOfUnit (unitPart f) 1

local instance tangentCoefficientInvertible (a : ℕ → A) :
    Invertible (PowerSeries.coeff 1 (tangentPowerSeriesOfCoefficients a)) where
  invOf := 1
  invOf_mul_self := by simp
  mul_invOf_self := by simp

/-- Compositional inverse of the corpus's arbitrary tangent-to-identity series. -/
def inverseCoordinate (a : ℕ → A) : PowerSeries A :=
  (tangentPowerSeriesOfCoefficients a).substInv

@[simp] theorem inverseCoordinate_constantCoeff (a : ℕ → A) :
    (inverseCoordinate a).constantCoeff = 0 := by simp [inverseCoordinate]

@[simp] theorem inverseCoordinate_coeff_one (a : ℕ → A) :
    PowerSeries.coeff 1 (inverseCoordinate a) = 1 := by
  rw [inverseCoordinate, PowerSeries.coeff_one_substInv]
  rfl

theorem coordinate_subst_inverse (a : ℕ → A) :
    (tangentPowerSeriesOfCoefficients a).subst (inverseCoordinate a) = PowerSeries.X :=
  PowerSeries.subst_substInv_right _ (tangentPowerSeriesOfCoefficients_constantCoeff a)

theorem inverse_subst_coordinate (a : ℕ → A) :
    (inverseCoordinate a).subst (tangentPowerSeriesOfCoefficients a) = PowerSeries.X :=
  PowerSeries.subst_substInv_left _ (tangentPowerSeriesOfCoefficients_constantCoeff a)

theorem coordinate_eq_unitPart_mul_X (a : ℕ → A) :
    tangentPowerSeriesOfCoefficients a =
      unitPart (tangentPowerSeriesOfCoefficients a) * PowerSeries.X := by
  simpa only [tangentPowerSeriesOfCoefficients_constantCoeff, map_zero, add_zero, unitPart]
    using PowerSeries.eq_shift_mul_X_add_const (tangentPowerSeriesOfCoefficients a)

theorem inverseCoordinate_eq_unitPart_mul_X (a : ℕ → A) :
    inverseCoordinate a = unitPart (inverseCoordinate a) * PowerSeries.X := by
  simpa only [inverseCoordinate_constantCoeff, map_zero, add_zero, unitPart]
    using PowerSeries.eq_shift_mul_X_add_const (inverseCoordinate a)

/-- The unit factors of inverse coordinates are themselves reciprocal after substitution. -/
theorem unitPart_coordinate_subst_inverse (a : ℕ → A) :
    (unitPart (tangentPowerSeriesOfCoefficients a)).subst (inverseCoordinate a) *
      unitPart (inverseCoordinate a) = 1 := by
  have hg := PowerSeries.HasSubst.of_constantCoeff_zero' (inverseCoordinate_constantCoeff a)
  apply PowerSeries.mul_X_cancel
  calc
    _ = (unitPart (tangentPowerSeriesOfCoefficients a)).subst (inverseCoordinate a) *
        inverseCoordinate a := by rw [mul_assoc, ← inverseCoordinate_eq_unitPart_mul_X]
    _ = (tangentPowerSeriesOfCoefficients a).subst (inverseCoordinate a) := by
      conv_rhs => rw [coordinate_eq_unitPart_mul_X]
      rw [PowerSeries.subst_mul hg, PowerSeries.subst_X hg]
    _ = 1 * PowerSeries.X := by rw [coordinate_subst_inverse, one_mul]

/-- The ordinary derivatives satisfy the formal inverse-function theorem. -/
theorem derivative_coordinate_subst_inverse (a : ℕ → A) :
    (PowerSeries.derivative A (tangentPowerSeriesOfCoefficients a)).subst (inverseCoordinate a) *
      PowerSeries.derivative A (inverseCoordinate a) = 1 := by
  have hg := PowerSeries.HasSubst.of_constantCoeff_zero' (inverseCoordinate_constantCoeff a)
  have h := congrArg (PowerSeries.derivative A) (coordinate_subst_inverse a)
  simpa only [PowerSeries.derivative_subst A hg, PowerSeries.derivative_X] using h

/-- Reciprocal logarithmic derivatives for every formal coordinate, integrally. -/
theorem reciprocal_logarithmicResponses (a : ℕ → A) :
    (logarithmicResponse (tangentPowerSeriesOfCoefficients a)).subst (inverseCoordinate a) *
      logarithmicResponse (inverseCoordinate a) = 1 := by
  have hg := PowerSeries.HasSubst.of_constantCoeff_zero' (inverseCoordinate_constantCoeff a)
  have hU := congrArg (PowerSeries.subst (inverseCoordinate a))
    (PowerSeries.invOfUnit_mul (unitPart (tangentPowerSeriesOfCoefficients a)) 1 (by simp))
  have hOne : PowerSeries.subst (inverseCoordinate a) (1 : PowerSeries A) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hg, map_one]
  rw [PowerSeries.subst_mul hg, hOne] at hU
  have hV := PowerSeries.invOfUnit_mul (unitPart (inverseCoordinate a)) 1 (by simp)
  rw [logarithmicResponse, PowerSeries.subst_mul hg, logarithmicResponse]
  calc
    _ = ((PowerSeries.derivative A (tangentPowerSeriesOfCoefficients a)).subst (inverseCoordinate a) *
          PowerSeries.derivative A (inverseCoordinate a)) *
        (((PowerSeries.invOfUnit (unitPart (tangentPowerSeriesOfCoefficients a)) 1).subst
            (inverseCoordinate a) * PowerSeries.invOfUnit (unitPart (inverseCoordinate a)) 1) *
          ((unitPart (tangentPowerSeriesOfCoefficients a)).subst (inverseCoordinate a) *
            unitPart (inverseCoordinate a))) := by
      rw [unitPart_coordinate_subst_inverse]
      ring
    _ = ((PowerSeries.derivative A (tangentPowerSeriesOfCoefficients a)).subst (inverseCoordinate a) *
          PowerSeries.derivative A (inverseCoordinate a)) *
        (((PowerSeries.invOfUnit (unitPart (tangentPowerSeriesOfCoefficients a)) 1).subst
            (inverseCoordinate a) *
            (unitPart (tangentPowerSeriesOfCoefficients a)).subst (inverseCoordinate a)) *
          (PowerSeries.invOfUnit (unitPart (inverseCoordinate a)) 1 *
            unitPart (inverseCoordinate a))) := by ring
    _ = 1 := by rw [derivative_coordinate_subst_inverse, hU, hV, mul_one, mul_one]

/-- The direct inverse agrees with the existing universal-coefficient construction. -/
theorem inverseCoordinate_eq_specializedInverse [Algebra ℂ A] (a : ℕ → A) :
    inverseCoordinate a = tangentInversePowerSeriesOfCoefficients a := by
  exact (powerSeries_subst_rightInverse_unique
    (tangentPowerSeriesOfCoefficients_constantCoeff a)
    (tangentInversePowerSeriesOfCoefficients_constantCoeff a)
    (inverse_subst_coordinate a) (tangentPowerSeries_subst_tangentInverse a)).symm

/-- The full free coefficient family inherits logarithmic reciprocity under inversion. -/
theorem specializedInverse_logarithmicResponses [Algebra ℂ A] (a : ℕ → A) :
    (logarithmicResponse (tangentPowerSeriesOfCoefficients a)).subst
        (tangentInversePowerSeriesOfCoefficients a) *
      logarithmicResponse (tangentInversePowerSeriesOfCoefficients a) = 1 := by
  rw [← inverseCoordinate_eq_specializedInverse]
  exact reciprocal_logarithmicResponses a

end GaloisForLFunctions.KodairaParshinAbc.Periods

#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.constantCoeff_unitPart
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.inverseCoordinate_constantCoeff
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.inverseCoordinate_coeff_one
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.coordinate_subst_inverse
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.inverse_subst_coordinate
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.coordinate_eq_unitPart_mul_X
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.inverseCoordinate_eq_unitPart_mul_X
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.unitPart_coordinate_subst_inverse
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.derivative_coordinate_subst_inverse
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.reciprocal_logarithmicResponses
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.inverseCoordinate_eq_specializedInverse
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.specializedInverse_logarithmicResponses

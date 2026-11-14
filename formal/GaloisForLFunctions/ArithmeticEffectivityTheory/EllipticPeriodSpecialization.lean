import GaloisForLFunctions.EisensteinDegeneration.PeriodImage
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticFormalEulerProduct

/-!
# Boundary orders of the actual elliptic Euler product

The formal product over the actual places and the point-count zeta series
are inverse units. Both detect regularity at the origin. A change of period
line contributes its own boundary length, even when the arithmetic factors
cancel each other.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

open PowerSeries EisensteinDegeneration

noncomputable section

/-- The actual place product, with inverse supplied by the point-count zeta series. -/
def ellipticEulerPeriodUnit : (PowerSeries ℂ)ˣ where
  val := ellipticEulerProduct
  inv := zeta
  val_inv := by
    rw [← ellipticEulerProduct_inv_eq_zeta]
    exact PowerSeries.mul_invOfUnit _ 1 ellipticEulerProduct_constantCoeff
  inv_val := by
    rw [← ellipticEulerProduct_inv_eq_zeta]
    exact PowerSeries.invOfUnit_mul _ 1 ellipticEulerProduct_constantCoeff

/-- The actual Euler product cannot conceal a pole of a formal family. -/
theorem ellipticEulerProduct_detects_regular (f : LaurentSeries ℂ) :
    Regular (f * (ellipticEulerProduct : LaurentSeries ℂ)) ↔ Regular f :=
  regular_mul_unit_iff f ellipticEulerPeriodUnit

/-- The point-count zeta series has the same pole-detection property. -/
theorem ellipticZeta_detects_regular (f : LaurentSeries ℂ) :
    Regular (f * (zeta : LaurentSeries ℂ)) ↔ Regular f :=
  regular_mul_unit_iff f ellipticEulerPeriodUnit⁻¹

/-- The leading boundary coefficient remains the value of the original family. -/
theorem ellipticEulerPeriod_boundary (m : ℕ) (f : PowerSeries ℂ) :
    coeff m (periodImage m ellipticEulerPeriodUnit f) = constantCoeff f := by
  rw [periodImage_coeff_boundary]
  change constantCoeff ellipticEulerProduct * constantCoeff f = _
  rw [ellipticEulerProduct_constantCoeff, one_mul]

/-- The boundary order is independent of the arithmetic Euler product. -/
theorem ellipticEulerPeriod_order (m : ℕ) (f : PowerSeries ℂ) :
    (periodImage m ellipticEulerPeriodUnit f).order = m + f.order :=
  periodImage_order m ellipticEulerPeriodUnit f

/-- Dividing a period-shifted elliptic Euler product remains regular exactly up to its
boundary order. -/
theorem ellipticEulerPeriod_division_iff (m n : ℕ) :
    Regular (HahnSeries.single (-(n : ℤ)) (1 : ℂ) *
      ((periodImage m ellipticEulerPeriodUnit 1 : PowerSeries ℂ) : LaurentSeries ℂ)) ↔
      n ≤ m :=
  regular_shift_period_iff m n ellipticEulerPeriodUnit

/-- Arithmetic inversion cancels the Euler product but retains both period-map orders. -/
theorem ellipticEulerZeta_period_composition (m n : ℕ) (f : PowerSeries ℂ) :
    periodImage m ellipticEulerPeriodUnit
      (periodImage n ellipticEulerPeriodUnit⁻¹ f) = X ^ (m + n) * f := by
  rw [periodImage_comp]
  simp only [mul_inv_cancel, periodImage, Units.val_one, one_mul]

/-- The weight-ring length of the elliptic boundary quotient is exactly the imposed order. -/
theorem ellipticEulerPeriod_boundary_length (m : ℕ) :
    Module.length (PowerSeries ℂ)
      (PowerSeries ℂ ⧸ Ideal.span {X ^ m * ellipticEulerProduct}) = m :=
  periodQuotient_length m ellipticEulerPeriodUnit

end

end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

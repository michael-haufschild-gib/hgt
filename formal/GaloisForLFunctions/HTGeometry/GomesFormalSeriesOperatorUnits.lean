import GaloisForLFunctions.HTGeometry.GomesFormalSeriesOperatorAlgebra
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Invertible formal-series operators and the geometric resolvent

A formal-series differentiation operator is invertible exactly when its constant
coefficient is nonzero. The geometric series is a concrete example: its actual
operator is a two-sided inverse of one minus differentiation.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- The constant term completely controls invertibility of an actual formal-series operator. -/
theorem gomesFormalSeriesPolynomialOperator_isUnit_iff (F : PowerSeries K) :
    IsUnit (gomesFormalSeriesPolynomialOperator K F) ↔ PowerSeries.coeff 0 F ≠ 0 := by
  constructor
  · intro h hz
    have hi := ((Module.End.isUnit_iff _).mp h).1
    have hone : gomesFormalSeriesPolynomialOperator K F 1 = 0 := by
      rw [← gomesDividedMonomialBasis_zero K, gomesFormalSeriesPolynomialOperator_basis,
        gomesFormalSeriesBasisImage_zero, hz, zero_smul]
    have hzero : (1 : K[X]) = 0 := hi (by rw [hone, map_zero])
    exact one_ne_zero hzero
  · intro h
    have hf : IsUnit F := by
      rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff,
        isUnit_iff_ne_zero]
      exact h
    exact hf.map (gomesFormalSeriesPolynomialAlgHom K)

omit [CharZero K] in
/-- The geometric formal series is a right inverse of one minus the formal variable. -/
theorem gomesFormalGeometricSeries_right_inverse :
    gomesFormalGeometricSeries K * (1 - PowerSeries.X) = 1 := by
  rw [mul_sub, mul_one]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp only [map_sub, gomesFormalGeometricSeries_coeff, PowerSeries.coeff_zero_mul_X,
        PowerSeries.coeff_zero_one, sub_zero]
  | succ n =>
      simp only [map_sub, gomesFormalGeometricSeries_coeff, PowerSeries.coeff_succ_mul_X,
        sub_self, PowerSeries.coeff_one, Nat.succ_ne_zero, if_false]

omit [CharZero K] in
/-- Commutativity gives the matching left inverse without any convergence argument. -/
theorem gomesFormalGeometricSeries_left_inverse :
    (1 - PowerSeries.X) * gomesFormalGeometricSeries K = 1 := by
  rw [mul_comm, gomesFormalGeometricSeries_right_inverse]

/-- The geometric-series polynomial operator is a genuine right inverse of one minus differentiation. -/
theorem gomesFormalGeometricOperator_right_inverse :
    (gomesFormalSeriesPolynomialOperator K (gomesFormalGeometricSeries K)).comp
      (1 - Polynomial.derivative) = 1 := by
  have h := congrArg (gomesFormalSeriesPolynomialAlgHom K) (gomesFormalGeometricSeries_right_inverse K)
  simpa only [map_mul, map_sub, map_one, gomesFormalSeriesPolynomialAlgHom_apply,
    gomesFormalSeriesPolynomialOperator_X, Module.End.mul_eq_comp] using h

/-- The same operator is also a left inverse, so the entire polynomial forcing problem is solved. -/
theorem gomesFormalGeometricOperator_left_inverse :
    (1 - Polynomial.derivative : Module.End K K[X]).comp
      (gomesFormalSeriesPolynomialOperator K (gomesFormalGeometricSeries K)) = 1 := by
  have h := congrArg (gomesFormalSeriesPolynomialAlgHom K) (gomesFormalGeometricSeries_left_inverse K)
  simpa only [map_mul, map_sub, map_one, gomesFormalSeriesPolynomialAlgHom_apply,
    gomesFormalSeriesPolynomialOperator_X, Module.End.mul_eq_comp] using h

end GaloisForLFunctions.HTGeometry

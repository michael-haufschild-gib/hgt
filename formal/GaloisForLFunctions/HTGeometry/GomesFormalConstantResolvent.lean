import GaloisForLFunctions.HTGeometry.GomesFormalSeriesOperatorUnits

/-!
# Formal symbols for all nonzero constant-coefficient resolvents

For a scalar unit `a`, the symbol with coefficient `-a^(-(n+1))` is the exact
inverse of the formal variable minus `a`. Its polynomial operator is consequently
the inverse of differentiation minus `a`, uniformly for every nonzero scalar.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- The complete formal symbol of the nonzero constant-coefficient resolvent. -/
def gomesFormalConstantResolventSymbol (a : Kˣ) : PowerSeries K :=
  PowerSeries.mk fun n => -((a : K)⁻¹ ^ (n + 1))

omit [CharZero K] in
/-- Every resolvent coefficient is given by the exact inverse scalar power. -/
theorem gomesFormalConstantResolventSymbol_coeff (a : Kˣ) (n : ℕ) :
    PowerSeries.coeff n (gomesFormalConstantResolventSymbol K a) = -((a : K)⁻¹ ^ (n + 1)) :=
  PowerSeries.coeff_mk n _

omit [CharZero K] in
/-- The full formal resolvent is a right inverse of the shifted formal variable. -/
theorem gomesFormalConstantResolventSymbol_right_inverse (a : Kˣ) :
    gomesFormalConstantResolventSymbol K a * (PowerSeries.X - PowerSeries.C (a : K)) = 1 := by
  rw [mul_sub]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp only [map_sub, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mul_C,
        gomesFormalConstantResolventSymbol_coeff, zero_add, pow_one, zero_sub,
        neg_mul, neg_neg, inv_mul_cancel₀ a.ne_zero, PowerSeries.coeff_zero_one]
  | succ n =>
      simp only [map_sub, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C,
        gomesFormalConstantResolventSymbol_coeff, PowerSeries.coeff_one, Nat.succ_ne_zero, if_false]
      rw [pow_succ ((a : K)⁻¹) (n + 1), neg_mul, mul_assoc, inv_mul_cancel₀ a.ne_zero, mul_one, sub_self]

omit [CharZero K] in
/-- The formal resolvent also gives the matching left inverse. -/
theorem gomesFormalConstantResolventSymbol_left_inverse (a : Kˣ) :
    (PowerSeries.X - PowerSeries.C (a : K)) * gomesFormalConstantResolventSymbol K a = 1 := by
  rw [mul_comm, gomesFormalConstantResolventSymbol_right_inverse]

/-- Its actual polynomial operator is a right inverse of the constant connection. -/
theorem gomesFormalConstantResolventOperator_right_inverse (a : Kˣ) :
    (gomesFormalSeriesPolynomialOperator K (gomesFormalConstantResolventSymbol K a)).comp
      (Polynomial.derivative - algebraMap K (Module.End K K[X]) (a : K)) = 1 := by
  have h := congrArg (gomesFormalSeriesPolynomialAlgHom K)
    (gomesFormalConstantResolventSymbol_right_inverse K a)
  rw [← PowerSeries.algebraMap_eq] at h
  simpa only [map_mul, map_sub, map_one, AlgHom.commutes,
    gomesFormalSeriesPolynomialAlgHom_apply, gomesFormalSeriesPolynomialOperator_X,
    Module.End.mul_eq_comp] using h

/-- The same operator is a left inverse, giving existence and uniqueness for every polynomial forcing. -/
theorem gomesFormalConstantResolventOperator_left_inverse (a : Kˣ) :
    (Polynomial.derivative - algebraMap K (Module.End K K[X]) (a : K)).comp
      (gomesFormalSeriesPolynomialOperator K (gomesFormalConstantResolventSymbol K a)) = 1 := by
  have h := congrArg (gomesFormalSeriesPolynomialAlgHom K)
    (gomesFormalConstantResolventSymbol_left_inverse K a)
  rw [← PowerSeries.algebraMap_eq] at h
  simpa only [map_mul, map_sub, map_one, AlgHom.commutes,
    gomesFormalSeriesPolynomialAlgHom_apply, gomesFormalSeriesPolynomialOperator_X,
    Module.End.mul_eq_comp] using h

end GaloisForLFunctions.HTGeometry

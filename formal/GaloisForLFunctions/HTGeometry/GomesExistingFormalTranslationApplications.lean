import GaloisForLFunctions.HTGeometry.GomesFormalExponentialTranslation
import GaloisForLFunctions.HTGeometry.GomesFormalSeriesOperatorUnits
import GaloisForLFunctions.HTGeometry.PowerSeriesCoeffSubalgebra
import GaloisForLFunctions.HTGeometry.PhysicalCharacteristicIncidence
import GaloisForLFunctions.HTGeometry.RationalPolePart
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslation

/-!
# Existing exponential symbols act as exact polynomial translations

This applies the complete formal functional calculus to the corpus's coefficient
subalgebra exponential, physical incidence exponential and quotient, pole-part
translation, and spectral even/odd exponential symbols. Every statement concerns
actual polynomial endomorphisms, with no analytic or nonvanishing premise.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- The existing coefficient-subalgebra exponential is the rescaled canonical formal exponential. -/
theorem gomesExpScaled_eq_rescale (c : K) :
    expScaled c = PowerSeries.rescale c (PowerSeries.exp K) := by
  apply PowerSeries.ext
  intro n
  simp [expScaled, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, mul_comm]

/-- The corpus's coefficient-subalgebra exponential acts by actual translation. -/
theorem gomesExpScaledOperator_eq_taylor (c : K) :
    gomesFormalSeriesPolynomialOperator K (expScaled c) = Polynomial.taylor c := by
  rw [gomesExpScaled_eq_rescale, gomesFormalExponentialOperator_eq_taylor]

/-- Existing pole-part translation is the exact formal exponential of differentiation. -/
theorem gomesPolyTranslate_eq_formalExponential (c : K) (P : K[X]) :
    polyTranslate c P =
      gomesFormalSeriesPolynomialOperator K (PowerSeries.rescale c (PowerSeries.exp K)) P := by
  rw [polyTranslate_apply, gomesFormalExponentialOperator_apply]

/-- The actual incidence exponential acts as polynomial translation for every complex parameter. -/
theorem gomesPhysicalFormalExponentialOperator (c : ℂ) :
    gomesFormalSeriesPolynomialOperator ℂ (physicalFormalExponential c) = Polynomial.taylor c :=
  gomesFormalExponentialOperator_eq_taylor ℂ c

/-- The existing incidence quotient factors exact finite translation differences through differentiation. -/
theorem gomesPhysicalTranslationDifference_factorization (c : ℂ) :
    Polynomial.taylor c - (1 : Module.End ℂ ℂ[X]) =
      Polynomial.derivative * gomesFormalSeriesPolynomialOperator ℂ (physicalFormalExponentialQuotient c) := by
  have h := congrArg (gomesFormalSeriesPolynomialAlgHom ℂ)
    (physicalFormalExponential_sub_one_eq_X_mul_quotient c)
  simpa only [map_sub, map_one, map_mul, gomesFormalSeriesPolynomialAlgHom_apply,
    gomesPhysicalFormalExponentialOperator, gomesFormalSeriesPolynomialOperator_X] using h

/-- The incidence quotient operator is invertible exactly away from the zero translation parameter. -/
theorem gomesPhysicalTranslationQuotient_isUnit_iff (c : ℂ) :
    IsUnit (gomesFormalSeriesPolynomialOperator ℂ (physicalFormalExponentialQuotient c)) ↔ c ≠ 0 := by
  rw [gomesFormalSeriesPolynomialOperator_isUnit_iff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    physicalFormalExponentialQuotient_constantCoeff]

/-- The existing even spectral exponential acts as the sum of opposite imaginary translations. -/
theorem gomesSpectralEvenExponentialOperator (x : ℝ) :
    gomesFormalSeriesPolynomialOperator ℂ (RHTower.spectralEvenExponentialPowerSeries x) =
      Polynomial.taylor ((x : ℂ) * Complex.I) + Polynomial.taylor (-((x : ℂ) * Complex.I)) := by
  change gomesFormalSeriesPolynomialAlgHom ℂ (_ + _) = _
  rw [map_add, gomesFormalSeriesPolynomialAlgHom_apply, gomesFormalSeriesPolynomialAlgHom_apply,
    gomesFormalExponentialOperator_eq_taylor, gomesFormalExponentialOperator_eq_taylor]

/-- The existing odd spectral exponential acts as the difference of opposite imaginary translations. -/
theorem gomesSpectralOddExponentialOperator (x : ℝ) :
    gomesFormalSeriesPolynomialOperator ℂ (RHTower.spectralOddExponentialPowerSeries x) =
      Polynomial.taylor ((x : ℂ) * Complex.I) - Polynomial.taylor (-((x : ℂ) * Complex.I)) := by
  change gomesFormalSeriesPolynomialAlgHom ℂ (_ - _) = _
  rw [map_sub, gomesFormalSeriesPolynomialAlgHom_apply, gomesFormalSeriesPolynomialAlgHom_apply,
    gomesFormalExponentialOperator_eq_taylor, gomesFormalExponentialOperator_eq_taylor]

end GaloisForLFunctions.HTGeometry

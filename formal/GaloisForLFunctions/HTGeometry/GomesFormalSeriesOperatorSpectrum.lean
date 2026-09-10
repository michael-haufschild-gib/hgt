import GaloisForLFunctions.HTGeometry.GomesFormalSeriesOperatorUnits
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Algebraic spectra of formal-series differentiation operators

The zeroth formal coefficient controls the entire algebraic spectrum in the algebra
of polynomial endomorphisms. This follows from the exact invertibility criterion,
without a topology, norm, or convergence argument.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- Scalar spectral shifts are transported exactly to subtraction of a constant formal series. -/
theorem gomesFormalSeriesPolynomialOperator_spectral_shift (F : PowerSeries K) (r : K) :
    algebraMap K (Module.End K K[X]) r - gomesFormalSeriesPolynomialOperator K F =
      gomesFormalSeriesPolynomialOperator K (algebraMap K (PowerSeries K) r - F) := by
  change algebraMap K (Module.End K K[X]) r - gomesFormalSeriesPolynomialAlgHom K F =
    gomesFormalSeriesPolynomialAlgHom K (algebraMap K (PowerSeries K) r - F)
  rw [map_sub, AlgHom.commutes]

/-- Spectral membership of any formal-series differentiation operator is exactly its constant symbol. -/
theorem gomesFormalSeriesPolynomialOperator_mem_spectrum_iff (F : PowerSeries K) (r : K) :
    r ∈ spectrum K (gomesFormalSeriesPolynomialOperator K F) ↔ r = PowerSeries.coeff 0 F := by
  rw [spectrum.mem_iff, gomesFormalSeriesPolynomialOperator_spectral_shift,
    gomesFormalSeriesPolynomialOperator_isUnit_iff, map_sub, PowerSeries.algebraMap_eq,
    PowerSeries.coeff_zero_C]
  simp only [not_not, sub_eq_zero]

/-- The full algebraic spectrum is a singleton, even for an infinite formal operator series. -/
theorem gomesFormalSeriesPolynomialOperator_spectrum (F : PowerSeries K) :
    spectrum K (gomesFormalSeriesPolynomialOperator K F) = {PowerSeries.coeff 0 F} := by
  ext r
  rw [gomesFormalSeriesPolynomialOperator_mem_spectrum_iff, Set.mem_singleton_iff]

/-- Spectral equality forgets exactly all formal coefficients beyond the constant term. -/
theorem gomesFormalSeriesPolynomialOperator_spectrum_eq_iff (F G : PowerSeries K) :
    spectrum K (gomesFormalSeriesPolynomialOperator K F) =
      spectrum K (gomesFormalSeriesPolynomialOperator K G) ↔
        PowerSeries.coeff 0 F = PowerSeries.coeff 0 G := by
  constructor
  · intro h
    have hf := (gomesFormalSeriesPolynomialOperator_mem_spectrum_iff K F (PowerSeries.coeff 0 F)).mpr rfl
    rw [h] at hf
    exact (gomesFormalSeriesPolynomialOperator_mem_spectrum_iff K G _).mp hf
  · intro h
    rw [gomesFormalSeriesPolynomialOperator_spectrum, gomesFormalSeriesPolynomialOperator_spectrum, h]

/-- Arbitrary first-order formal perturbations preserve the complete algebraic spectrum. -/
theorem gomesFormalSeriesPolynomialOperator_spectral_perturbation (F : PowerSeries K) (c : K) :
    spectrum K (gomesFormalSeriesPolynomialOperator K (F + c • PowerSeries.X)) =
      spectrum K (gomesFormalSeriesPolynomialOperator K F) := by
  apply (gomesFormalSeriesPolynomialOperator_spectrum_eq_iff K _ _).mpr
  simp only [map_add, map_smul, PowerSeries.coeff_X, zero_ne_one, if_false, smul_zero, add_zero]

/-- The spectrally invisible first-order perturbation family still consists of distinct actual operators. -/
theorem gomesFormalSeriesPolynomialOperator_spectral_family_injective (F : PowerSeries K) :
    Function.Injective (fun c : K => gomesFormalSeriesPolynomialOperator K (F + c • PowerSeries.X)) := by
  intro c d h
  have hs := gomesFormalSeriesPolynomialOperator_injective K h
  have hc := congrArg (PowerSeries.coeff 1) hs
  simp only [map_add, map_smul, PowerSeries.coeff_X, ite_true, smul_eq_mul, mul_one] at hc
  exact add_left_cancel hc

/-- The constant input is always an actual eigenvector for the unique spectral value. -/
theorem gomesFormalSeriesPolynomialOperator_constant_eigenvector (F : PowerSeries K) :
    gomesFormalSeriesPolynomialOperator K F 1 = PowerSeries.coeff 0 F • (1 : K[X]) := by
  rw [← gomesDividedMonomialBasis_zero K, gomesFormalSeriesPolynomialOperator_basis,
    gomesFormalSeriesBasisImage_zero]

/-- The geometric inverse has algebraic spectrum exactly one. -/
theorem gomesFormalGeometricOperator_spectrum :
    spectrum K (gomesFormalSeriesPolynomialOperator K (gomesFormalGeometricSeries K)) = {1} := by
  rw [gomesFormalSeriesPolynomialOperator_spectrum, gomesFormalGeometricSeries_coeff]

end GaloisForLFunctions.HTGeometry

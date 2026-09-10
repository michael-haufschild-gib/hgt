import GaloisForLFunctions.HTGeometry.GomesDividedMonomialBasis
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Formal series acting on polynomials by locally finite differentiation

A formal series specifies a finite triangular image of each divided monomial.
Extending from the basis gives an actual linear endomorphism of polynomials.
No convergence condition is imposed: an input basis vector uses only finitely many
series coefficients. The constructed operator commutes with differentiation.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- A formal series sends the n-th divided monomial to its finite triangular convolution. -/
def gomesFormalSeriesBasisImage (F : PowerSeries K) (n : ℕ) : K[X] :=
  ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff (n - j) F • gomesDividedMonomialBasis K j

/-- The formal-series operator is the linear extension of the finite basis images. -/
def gomesFormalSeriesPolynomialOperator (F : PowerSeries K) : Module.End K K[X] :=
  (gomesDividedMonomialBasis K).constr K (gomesFormalSeriesBasisImage K F)

/-- The operator realizes its prescribed finite image on each divided monomial. -/
theorem gomesFormalSeriesPolynomialOperator_basis (F : PowerSeries K) (n : ℕ) :
    gomesFormalSeriesPolynomialOperator K F (gomesDividedMonomialBasis K n) =
      gomesFormalSeriesBasisImage K F n :=
  (gomesDividedMonomialBasis K).constr_basis K (gomesFormalSeriesBasisImage K F) n

/-- The image of the constant seed uses only the zeroth formal coefficient. -/
theorem gomesFormalSeriesBasisImage_zero (F : PowerSeries K) :
    gomesFormalSeriesBasisImage K F 0 = PowerSeries.coeff 0 F • gomesDividedMonomialBasis K 0 := by
  simp [gomesFormalSeriesBasisImage]

/-- Differentiation lowers the finite image chain exactly. -/
theorem gomesFormalSeriesBasisImage_derivative_succ (F : PowerSeries K) (n : ℕ) :
    (gomesFormalSeriesBasisImage K F (n + 1)).derivative = gomesFormalSeriesBasisImage K F n := by
  rw [gomesFormalSeriesBasisImage, map_sum, Finset.sum_range_succ']
  simp only [map_smul, gomesDividedMonomialBasis_derivative_succ,
    gomesDividedMonomialBasis_derivative_zero, smul_zero, add_zero, Nat.add_sub_add_right]
  rfl

/-- The constant coefficient of the n-th image is precisely the n-th formal coefficient. -/
theorem gomesFormalSeriesBasisImage_coeff_zero (F : PowerSeries K) (n : ℕ) :
    (gomesFormalSeriesBasisImage K F n).coeff 0 = PowerSeries.coeff n F := by
  change (Polynomial.lcoeff K 0) (gomesFormalSeriesBasisImage K F n) = _
  rw [gomesFormalSeriesBasisImage, map_sum]
  simp only [map_smul]
  change (∑ j ∈ Finset.range (n + 1),
    PowerSeries.coeff (n - j) F • (gomesDividedMonomialBasis K j).coeff 0) = _
  simp [gomesDividedMonomialBasis_coeff_zero]

/-- Every formal-series operator genuinely commutes with polynomial differentiation. -/
theorem gomesFormalSeriesPolynomialOperator_commutes (F : PowerSeries K) :
    (gomesFormalSeriesPolynomialOperator K F).comp Polynomial.derivative =
      Polynomial.derivative.comp (gomesFormalSeriesPolynomialOperator K F) := by
  apply (gomesDividedMonomialBasis K).ext
  intro n
  cases n with
  | zero =>
      simp only [LinearMap.comp_apply, gomesDividedMonomialBasis_derivative_zero,
        map_zero, gomesFormalSeriesPolynomialOperator_basis, gomesFormalSeriesBasisImage_zero,
        map_smul, smul_zero]
  | succ n =>
      simp only [LinearMap.comp_apply, gomesDividedMonomialBasis_derivative_succ,
        gomesFormalSeriesPolynomialOperator_basis, gomesFormalSeriesBasisImage_derivative_succ]

/-- The formal coefficient sequence is recovered from actual operator outputs. -/
theorem gomesFormalSeriesPolynomialOperator_coeff_zero (F : PowerSeries K) (n : ℕ) :
    (gomesFormalSeriesPolynomialOperator K F (gomesDividedMonomialBasis K n)).coeff 0 =
      PowerSeries.coeff n F := by
  rw [gomesFormalSeriesPolynomialOperator_basis, gomesFormalSeriesBasisImage_coeff_zero]

/-- Distinct formal series always give distinct polynomial endomorphisms. -/
theorem gomesFormalSeriesPolynomialOperator_injective :
    Function.Injective (gomesFormalSeriesPolynomialOperator K) := by
  intro F G h
  apply PowerSeries.ext
  intro n
  have hn := congrArg (fun E : Module.End K K[X] => (E (gomesDividedMonomialBasis K n)).coeff 0) h
  simpa only [gomesFormalSeriesPolynomialOperator_coeff_zero] using hn

end GaloisForLFunctions.HTGeometry

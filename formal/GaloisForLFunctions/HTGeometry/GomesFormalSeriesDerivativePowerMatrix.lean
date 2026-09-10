import GaloisForLFunctions.HTGeometry.GomesResidueChainSymbolObservation
import GaloisForLFunctions.HTGeometry.GomesFormalSeriesOperatorAlgebra

/-!
# Formal differentiation series inside higher-derivative symmetry algebras

Every formal function of differentiation commutes with every derivative power.
Its finite formal matrix is faithful, and the first row separates its coefficients
into residue classes.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- Every formal differentiation operator is a symmetry of every derivative power. -/
theorem gomesFormalSeriesPolynomialOperator_mem_derivativePowerCommutant
    (m : ℕ) (F : PowerSeries K) :
    gomesFormalSeriesPolynomialOperator K F ∈ gomesPolynomialDerivativePowerCommutantAlgebra K m := by
  rw [gomesPolynomialDerivativePowerCommutantAlgebra, gomesCentralizerSingleton_mem_iff]
  have h : Commute (gomesFormalSeriesPolynomialOperator K F)
      (Polynomial.derivative : Module.End K K[X]) :=
    gomesFormalSeriesPolynomialOperator_commutes K F
  exact (h.pow_right m).eq.symm

/-- Formal differentiation series as actual higher-derivative symmetries. -/
def gomesFormalSeriesDerivativePowerHom (m : ℕ) :
    PowerSeries K →ₐ[K] GomesPolynomialDerivativePowerCommutant K m :=
  (gomesFormalSeriesPolynomialAlgHom K).codRestrict
    (gomesPolynomialDerivativePowerCommutantAlgebra K m)
      (gomesFormalSeriesPolynomialOperator_mem_derivativePowerCommutant K m)

/-- Formal differentiation series represented in the full finite matrix model of a derivative power. -/
def gomesFormalSeriesDerivativePowerMatrixHom (m : ℕ) [NeZero m] :
    PowerSeries K →ₐ[K] Matrix (Fin m) (Fin m) (PowerSeries K) :=
  (gomesPolynomialDerivativePowerCommutantEquiv K m).toAlgHom.comp
    (gomesFormalSeriesDerivativePowerHom K m)

/-- The finite matrix model loses no formal differentiation symbol. -/
theorem gomesFormalSeriesDerivativePowerMatrixHom_injective (m : ℕ) [NeZero m] :
    Function.Injective (gomesFormalSeriesDerivativePowerMatrixHom K m) := by
  intro F G h
  change gomesPolynomialDerivativePowerCommutantEquiv K m (gomesFormalSeriesDerivativePowerHom K m F) =
    gomesPolynomialDerivativePowerCommutantEquiv K m (gomesFormalSeriesDerivativePowerHom K m G) at h
  have hs := (gomesPolynomialDerivativePowerCommutantEquiv K m).injective h
  exact gomesFormalSeriesPolynomialOperator_injective K (congrArg Subtype.val hs)

/-- The first matrix row records every formal coefficient, separated by its residue class. -/
theorem gomesFormalSeriesDerivativePowerMatrixHom_first_row
    (m : ℕ) [NeZero m] (F : PowerSeries K) (j : Fin m) (n : ℕ) :
    PowerSeries.coeff n (gomesFormalSeriesDerivativePowerMatrixHom K m F 0 j) =
      PowerSeries.coeff (n * m + j.val) F := by
  change PowerSeries.coeff n
    (gomesPolynomialDerivativePowerCommutantEquiv K m (gomesFormalSeriesDerivativePowerHom K m F) 0 j) = _
  rw [gomesPolynomialDerivativePowerCommutant_matrix_first_row]
  exact gomesFormalSeriesPolynomialOperator_coeff_zero K F (n * m + j.val)

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.GomesFormalConstantResolvent
import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionFullCommutant
import GaloisForLFunctions.HTGeometry.GomesPolynomialResolventSeries
import GaloisForLFunctions.HTGeometry.StokesWeylFourierSource
import GaloisForLFunctions.HTGeometry.SuperPoincarePolynomialReflection

/-!
# Formal-series reconstruction in existing operator representations

The generic classification is applied to the actual real constant connections,
complex Weyl derivative, and complex supertranslation derivative. Its geometric
operator also recovers the already formalized finite polynomial resolvent.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Every real constant connection has one unique formal-series description of each commuting map. -/
theorem gomesConstantConnection_full_commutant_unique_iff (a : ℝ) (E : Module.End ℝ ℝ[X]) :
    E ∈ gomesPolynomialConnectionCommutantAlgebra (C a) ↔
      ∃! F : PowerSeries ℝ, E = gomesFormalSeriesPolynomialOperator ℝ F := by
  rw [gomesPolynomialConstantConnection_commutant_algebra,
    gomesPolynomialDerivativeCommutant_mem_iff, gomesPolynomialDerivative_commutes_iff_series]

/-- Polynomial expressions in a constant connection are exactly the corresponding shifted derivative polynomials. -/
theorem gomesConstantConnection_aeval_formal_symbol (a : ℝ) (P : ℝ[X]) :
    (Polynomial.aeval (gomesPolynomialFirstOrderLinearMap (C a))) P =
      gomesFormalSeriesPolynomialOperator ℝ ((P.comp (X - C a) : ℝ[X]) : PowerSeries ℝ) := by
  rw [gomesFormalSeriesPolynomialOperator_polynomial, Polynomial.aeval_comp,
    map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  have h : (Polynomial.derivative : Module.End ℝ ℝ[X]) - algebraMap ℝ (Module.End ℝ ℝ[X]) a =
      gomesPolynomialFirstOrderLinearMap (C a) := by
    apply LinearMap.ext
    intro Q
    change Q.derivative - a • Q = Q.derivative - C a * Q
    rw [smul_eq_C_mul]
  rw [h]

/-- Every constant connection has an actual symmetry beyond every polynomial in that connection itself. -/
theorem gomesConstantConnection_nonpolynomial_operator_symmetry (a : ℝ) :
    ∃ E : Module.End ℝ ℝ[X], E ∈ gomesPolynomialConnectionCommutantAlgebra (C a) ∧
      ∀ P : ℝ[X], E ≠ (Polynomial.aeval (gomesPolynomialFirstOrderLinearMap (C a))) P := by
  refine ⟨gomesFormalSeriesPolynomialOperator ℝ (gomesFormalGeometricSeries ℝ), ?_, ?_⟩
  · rw [gomesPolynomialConstantConnection_commutant_algebra]
    exact (gomesPolynomialDerivativeCommutant_mem_iff ℝ _).mpr
      (gomesFormalSeriesPolynomialOperator_commutes ℝ _)
  · intro P h
    rw [gomesConstantConnection_aeval_formal_symbol] at h
    exact gomesFormalGeometricSeries_not_polynomial ℝ (P.comp (X - C a))
      (gomesFormalSeriesPolynomialOperator_injective ℝ h)

/-- The actual derivative in the complex Weyl presentation has the full formal-series commutant. -/
theorem gomesWeylPolynomialDerivative_full_commutant_iff (E : Module.End ℂ ℂ[X]) :
    (E.comp GaloisForLFunctions.IrregularStokes.WeylFourier.polynomialDerivativeOperator =
      GaloisForLFunctions.IrregularStokes.WeylFourier.polynomialDerivativeOperator.comp E) ↔
        ∃! F : PowerSeries ℂ, E = gomesFormalSeriesPolynomialOperator ℂ F :=
  gomesPolynomialDerivative_commutes_iff_series ℂ E

/-- The actual complex derivative in the supertranslation representation has the same complete description. -/
theorem gomesSupertranslationPolynomialDerivative_full_commutant_iff (E : Module.End ℂ ℂ[X]) :
    (E.comp polynomialDerivativeEnd = polynomialDerivativeEnd.comp E) ↔
      ∃! F : PowerSeries ℂ, E = gomesFormalSeriesPolynomialOperator ℂ F :=
  gomesPolynomialDerivative_commutes_iff_series ℂ E

/-- The Weyl derivative admits a genuine commuting map outside all finite polynomial operator words. -/
theorem gomesWeylPolynomialDerivative_nonpolynomial_symmetry :
    ∃ E : Module.End ℂ ℂ[X],
      E.comp GaloisForLFunctions.IrregularStokes.WeylFourier.polynomialDerivativeOperator =
        GaloisForLFunctions.IrregularStokes.WeylFourier.polynomialDerivativeOperator.comp E ∧
      ∀ P : ℂ[X], E ≠ (Polynomial.aeval
        GaloisForLFunctions.IrregularStokes.WeylFourier.polynomialDerivativeOperator) P :=
  gomesPolynomialDerivative_nonpolynomial_symmetry ℂ

/-- The formal symbol recovers the existing finite resolvent solver for every nonzero constant coefficient. -/
theorem gomesFormalConstantResolvent_existing_solver (a : ℝˣ) (Q : ℝ[X]) :
    gomesPolynomialResolventSeries a Q =
      gomesFormalSeriesPolynomialOperator ℝ (gomesFormalConstantResolventSymbol ℝ a) Q := by
  apply (gomesPolynomialFirstOrderEquiv a).injective
  change gomesPolynomialFirstOrderOperator (C (a : ℝ)) (gomesPolynomialResolventSeries a Q) =
    gomesPolynomialFirstOrderOperator (C (a : ℝ))
      (gomesFormalSeriesPolynomialOperator ℝ (gomesFormalConstantResolventSymbol ℝ a) Q)
  rw [gomesPolynomialResolventSeries_solves]
  have h := congrArg (fun E : Module.End ℝ ℝ[X] => E Q)
    (gomesFormalConstantResolventOperator_left_inverse ℝ a)
  change (gomesFormalSeriesPolynomialOperator ℝ (gomesFormalConstantResolventSymbol ℝ a) Q).derivative -
    (a : ℝ) • gomesFormalSeriesPolynomialOperator ℝ (gomesFormalConstantResolventSymbol ℝ a) Q = Q at h
  change Q =
    (gomesFormalSeriesPolynomialOperator ℝ (gomesFormalConstantResolventSymbol ℝ a) Q).derivative -
      C (a : ℝ) * gomesFormalSeriesPolynomialOperator ℝ (gomesFormalConstantResolventSymbol ℝ a) Q
  rw [← smul_eq_C_mul]
  exact h.symm

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.GomesPolynomialDerivativeCommutant

/-!
# Faithful formal functional calculus and its polynomial boundary

The formal-series classification gives a faithful algebra action on polynomials.
The formal variable acts as differentiation, so ordinary polynomial functional
calculus embeds into it. The all-ones formal series gives an actual commuting
endomorphism that is not any polynomial in differentiation.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- Formal-series functional calculus as an algebra homomorphism into actual polynomial endomorphisms. -/
def gomesFormalSeriesPolynomialAlgHom : PowerSeries K →ₐ[K] Module.End K K[X] :=
  (gomesPolynomialDerivativeCommutantAlgebra K).val.comp
    (gomesPolynomialDerivativeCommutantEquiv K).symm.toAlgHom

/-- The algebra action is the previously constructed locally finite operator. -/
theorem gomesFormalSeriesPolynomialAlgHom_apply (F : PowerSeries K) :
    gomesFormalSeriesPolynomialAlgHom K F = gomesFormalSeriesPolynomialOperator K F := rfl

/-- Differentiation itself as an element of its full commutant. -/
def gomesPolynomialDerivativeSymmetry : GomesPolynomialDerivativeCommutant K :=
  ⟨Polynomial.derivative, (gomesPolynomialDerivativeCommutant_mem_iff K _).mpr rfl⟩

/-- The formal symbol of differentiation is the formal variable. -/
theorem gomesDerivativeCommutantSymbol_derivative :
    gomesDerivativeCommutantSymbol K (gomesPolynomialDerivativeSymmetry K) = PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  rw [gomesDerivativeCommutantSymbol_coeff]
  change (gomesDividedMonomialBasis K n).derivative.coeff 0 = _
  cases n with
  | zero => simp [gomesDividedMonomialBasis_derivative_zero, PowerSeries.coeff_X]
  | succ n => simp [gomesDividedMonomialBasis_derivative_succ,
      gomesDividedMonomialBasis_coeff_zero, PowerSeries.coeff_X]

/-- The formal variable acts by actual polynomial differentiation. -/
theorem gomesFormalSeriesPolynomialOperator_X :
    gomesFormalSeriesPolynomialOperator K PowerSeries.X = Polynomial.derivative := by
  have h := gomesFormalSeriesCommutingOperator_symbol K (gomesPolynomialDerivativeSymmetry K)
  rw [gomesDerivativeCommutantSymbol_derivative] at h
  exact congrArg Subtype.val h

/-- The formal functional calculus preserves products as actual operator composition. -/
theorem gomesFormalSeriesPolynomialOperator_mul (F G : PowerSeries K) :
    gomesFormalSeriesPolynomialOperator K (F * G) =
      (gomesFormalSeriesPolynomialOperator K F).comp (gomesFormalSeriesPolynomialOperator K G) :=
  (gomesFormalSeriesPolynomialAlgHom K).map_mul F G

/-- The formal functional calculus is faithful on every characteristic-zero coefficient field. -/
theorem gomesFormalSeriesPolynomialAlgHom_injective :
    Function.Injective (gomesFormalSeriesPolynomialAlgHom K) :=
  gomesFormalSeriesPolynomialOperator_injective K

/-- Ordinary polynomial functional calculus is exactly the polynomial part of formal-series calculus. -/
theorem gomesFormalSeriesPolynomialOperator_polynomial (P : K[X]) :
    gomesFormalSeriesPolynomialOperator K (P : PowerSeries K) =
      (Polynomial.aeval (Polynomial.derivative : Module.End K K[X])) P := by
  have h : (gomesFormalSeriesPolynomialAlgHom K).comp
      (Polynomial.coeToPowerSeries.algHom K) =
        Polynomial.aeval (Polynomial.derivative : Module.End K K[X]) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.coeToPowerSeries.algHom_apply,
      Algebra.algebraMap_self, PowerSeries.map_id, id_eq, Polynomial.coe_X,
      gomesFormalSeriesPolynomialAlgHom_apply, gomesFormalSeriesPolynomialOperator_X,
      Polynomial.aeval_X]
  have hp := congrArg (fun f : K[X] →ₐ[K] Module.End K K[X] => f P) h
  simpa only [AlgHom.comp_apply, Polynomial.coeToPowerSeries.algHom_apply,
    Algebra.algebraMap_self, PowerSeries.map_id, id_eq, gomesFormalSeriesPolynomialAlgHom_apply] using hp

/-- Evaluation at polynomial differentiation is faithful despite local nilpotence on each input. -/
theorem gomesPolynomialDerivative_aeval_injective :
    Function.Injective (Polynomial.aeval (R := K) (Polynomial.derivative : Module.End K K[X])) := by
  intro P Q h
  apply Polynomial.coe_injective K
  apply gomesFormalSeriesPolynomialOperator_injective K
  simpa only [gomesFormalSeriesPolynomialOperator_polynomial] using h

/-- The all-ones series has infinitely many nonzero formal coefficients. -/
def gomesFormalGeometricSeries : PowerSeries K := PowerSeries.mk fun _ => 1

omit [CharZero K] in
/-- Every coefficient of the formal geometric series is exactly one. -/
theorem gomesFormalGeometricSeries_coeff (n : ℕ) :
    PowerSeries.coeff n (gomesFormalGeometricSeries K) = 1 := PowerSeries.coeff_mk n _

omit [CharZero K] in
/-- The formal geometric series cannot be represented by any polynomial. -/
theorem gomesFormalGeometricSeries_not_polynomial (P : K[X]) :
    gomesFormalGeometricSeries K ≠ (P : PowerSeries K) := by
  intro h
  have hn := congrArg (PowerSeries.coeff (P.natDegree + 1)) h
  rw [gomesFormalGeometricSeries_coeff, Polynomial.coeff_coe,
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self P.natDegree)] at hn
  exact one_ne_zero hn

/-- A genuine differentiation symmetry exists beyond all finite-order polynomial operators. -/
theorem gomesPolynomialDerivative_nonpolynomial_symmetry :
    ∃ E : Module.End K K[X],
      E.comp Polynomial.derivative = Polynomial.derivative.comp E ∧
        ∀ P : K[X], E ≠ (Polynomial.aeval (Polynomial.derivative : Module.End K K[X])) P := by
  refine ⟨gomesFormalSeriesPolynomialOperator K (gomesFormalGeometricSeries K),
    gomesFormalSeriesPolynomialOperator_commutes K _, ?_⟩
  intro P h
  apply gomesFormalGeometricSeries_not_polynomial K P
  apply gomesFormalSeriesPolynomialOperator_injective K
  simpa only [gomesFormalSeriesPolynomialOperator_polynomial] using h

end GaloisForLFunctions.HTGeometry

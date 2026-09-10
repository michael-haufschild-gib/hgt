import GaloisForLFunctions.HTGeometry.GomesFormalSeriesOperatorAlgebra
import GaloisForLFunctions.HTGeometry.EisensteinUniform
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Formal exponential differentiation is actual polynomial translation

Translation already commutes with differentiation in the corpus. The complete
commutant classification identifies its formal symbol by constant coefficients,
so no analytic convergence or infinite operator sum is needed.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- Actual polynomial translation as an element of the full differentiation commutant. -/
def gomesTaylorCommutingOperator (c : K) : GomesPolynomialDerivativeCommutant K :=
  ⟨Polynomial.taylor c, (gomesPolynomialDerivativeCommutant_mem_iff K _).mpr (by
    apply LinearMap.ext
    intro P
    exact (derivative_taylor c P).symm)⟩

/-- The symbol of actual translation is the formal exponential of the scaled variable. -/
theorem gomesTaylorCommutingOperator_symbol (c : K) :
    gomesDerivativeCommutantSymbol K (gomesTaylorCommutingOperator K c) =
      PowerSeries.rescale c (PowerSeries.exp K) := by
  apply PowerSeries.ext
  intro n
  rw [gomesDerivativeCommutantSymbol_coeff]
  change (Polynomial.taylor c (gomesDividedMonomialBasis K n)).coeff 0 = _
  rw [Polynomial.taylor_coeff_zero, gomesDividedMonomialBasis_apply,
    Polynomial.eval_smul, Polynomial.eval_pow, Polynomial.eval_X,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp only [one_div, smul_eq_mul, map_inv₀, map_natCast]
  exact mul_comm _ _

/-- The complete formal exponential operator equals the actual Taylor translation map. -/
theorem gomesFormalExponentialOperator_eq_taylor (c : K) :
    gomesFormalSeriesPolynomialOperator K (PowerSeries.rescale c (PowerSeries.exp K)) =
      Polynomial.taylor c := by
  have h := congrArg Subtype.val
    (gomesFormalSeriesCommutingOperator_symbol K (gomesTaylorCommutingOperator K c))
  change gomesFormalSeriesPolynomialOperator K
    (gomesDerivativeCommutantSymbol K (gomesTaylorCommutingOperator K c)) = Polynomial.taylor c at h
  rwa [gomesTaylorCommutingOperator_symbol] at h

/-- On every polynomial, the infinite formal symbol produces exact substitution by X+c. -/
theorem gomesFormalExponentialOperator_apply (c : K) (P : K[X]) :
    gomesFormalSeriesPolynomialOperator K (PowerSeries.rescale c (PowerSeries.exp K)) P =
      P.comp (X + C c) := by
  rw [gomesFormalExponentialOperator_eq_taylor, Polynomial.taylor_apply]

/-- The formal exponential addition law becomes composition of actual polynomial translations. -/
theorem gomesFormalExponentialOperator_comp (c d : K) :
    (gomesFormalSeriesPolynomialOperator K (PowerSeries.rescale c (PowerSeries.exp K))).comp
      (gomesFormalSeriesPolynomialOperator K (PowerSeries.rescale d (PowerSeries.exp K))) =
        gomesFormalSeriesPolynomialOperator K (PowerSeries.rescale (c + d) (PowerSeries.exp K)) := by
  rw [← gomesFormalSeriesPolynomialOperator_mul, PowerSeries.exp_mul_exp_eq_exp_add]

/-- Every scaled formal exponential gives an invertible polynomial endomorphism, including zero scale. -/
theorem gomesFormalExponentialOperator_isUnit (c : K) :
    IsUnit (gomesFormalSeriesPolynomialOperator K (PowerSeries.rescale c (PowerSeries.exp K))) := by
  change IsUnit (gomesFormalSeriesPolynomialAlgHom K (PowerSeries.rescale c (PowerSeries.exp K)))
  exact ((PowerSeries.isUnit_exp K).map (PowerSeries.rescale c)).map (gomesFormalSeriesPolynomialAlgHom K)

end GaloisForLFunctions.HTGeometry

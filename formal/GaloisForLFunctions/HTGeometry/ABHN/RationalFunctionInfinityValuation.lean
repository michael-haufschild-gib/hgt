import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInversion
import Mathlib.RingTheory.LaurentSeries

/-!
# Comparing the infinity and `X`-adic rational-function valuations

After the coordinate change `t ↦ t⁻¹`, the `X`-adic valuation on `F(t)` is equivalent to the
valuation at infinity.  This is the valuation-level input for comparing their completions with
the Laurent-series local field.  The topological transport of the resulting completion is kept
separate.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped RatFunc WithZero

universe u

noncomputable section

/-- Pullback of the `X`-adic rational-function valuation along coordinate inversion. -/
noncomputable def rationalFunctionInversionComapPolynomialValuation
    (F : Type u) [Field F] : Valuation (RatFunc F) ℤᵐ⁰ :=
  (RatFunc.polynomialValuationX F).comap
    (rationalFunctionInversionAlgEquiv F).toRingHom

/-- The pullback valuation is trivial on the coefficient field. -/
theorem rationalFunctionInversionComapPolynomialValuation_isTrivialOn
    (F : Type u) [Field F] :
    (rationalFunctionInversionComapPolynomialValuation F).IsTrivialOn F := by
  classical
  constructor
  intro a ha
  change RatFunc.polynomialValuationX F
    (rationalFunctionInversionAlgEquiv F (algebraMap F (RatFunc F) a)) = 1
  rw [(rationalFunctionInversionAlgEquiv F).commutes]
  change (Polynomial.idealX F).valuation _ (RatFunc.C a) = 1
  rw [← RatFunc.algebraMap_C,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
  change Polynomial.C a ∉ Ideal.span {Polynomial.X}
  intro h
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff] at h
  exact ha (by simpa using h)

/-- Under coordinate inversion, the rational-function variable has positive valuation. -/
theorem one_lt_rationalFunctionInversionComapPolynomialValuation_X
    (F : Type u) [Field F] :
    1 < rationalFunctionInversionComapPolynomialValuation F RatFunc.X := by
  classical
  change 1 < RatFunc.polynomialValuationX F
    (rationalFunctionInversionAlgEquiv F RatFunc.X)
  rw [rationalFunctionInversionAlgEquiv_X, map_inv₀, Polynomial.valuation_X_eq_neg_one]
  rw [one_lt_inv_iff₀]
  constructor
  · exact WithZero.exp_pos
  · rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)

/-- Coordinate inversion identifies the infinity valuation with the `X`-adic valuation up to
valuation equivalence. -/
theorem rationalFunctionInftyValuation_isEquiv_inversionComapPolynomialValuation
    (F : Type u) [Field F] [DecidableEq (RatFunc F)] :
    (RatFunc.inftyValuation F).IsEquiv
      (rationalFunctionInversionComapPolynomialValuation F) := by
  letI : (rationalFunctionInversionComapPolynomialValuation F).IsTrivialOn F :=
    rationalFunctionInversionComapPolynomialValuation_isTrivialOn F
  exact (RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X
    (one_lt_rationalFunctionInversionComapPolynomialValuation_X F)).symm

end

end GaloisForLFunctions.HTGeometry.ABHN

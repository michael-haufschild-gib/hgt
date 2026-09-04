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

/-- A valuation subring containing a coefficient field is trivial on that field. -/
theorem valuationSubring_isTrivialOn_of_algebraMap_mem
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (A : ValuationSubring K)
    (hmem : ∀ c : F, algebraMap F K c ∈ A) :
    A.valuation.IsTrivialOn F := by
  constructor
  intro c hc
  let a : A := ⟨algebraMap F K c, hmem c⟩
  apply (A.valuation_eq_one_iff a).mp
  rw [isUnit_iff_exists_inv]
  refine ⟨⟨algebraMap F K c⁻¹, hmem c⁻¹⟩, ?_⟩
  apply Subtype.ext
  change algebraMap F K c * algebraMap F K c⁻¹ = 1
  rw [← map_mul]
  simp [hc]

/-- **Uniqueness of the rational-function place at infinity.**  A valuation ring on `F(X)` that
contains every coefficient constant and excludes `X` is exactly the valuation ring of the standard
infinity valuation. -/
theorem valuationSubring_eq_inftyValuation_of_algebraMap_mem_of_X_not_mem
    (F : Type*) [Field F] [DecidableEq (RatFunc F)]
    (A : ValuationSubring (RatFunc F))
    (hconst : ∀ c : F, algebraMap F (RatFunc F) c ∈ A)
    (hX : RatFunc.X ∉ A) :
    A = (RatFunc.inftyValuation F).valuationSubring := by
  letI : A.valuation.IsTrivialOn F :=
    valuationSubring_isTrivialOn_of_algebraMap_mem A hconst
  have hlt : 1 < A.valuation RatFunc.X := by
    rw [lt_iff_not_ge]
    intro hle
    apply hX
    simpa using hle
  have hequiv := RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hlt
  ext x
  simp only [show x ∈ A ↔ A.valuation x ≤ 1 by simp]
  simpa using hequiv x 1

end

end GaloisForLFunctions.HTGeometry.ABHN

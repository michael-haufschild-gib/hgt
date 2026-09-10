import GaloisForLFunctions.HTGeometry.GomesFormalSeriesPolynomialOperator
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# The full differentiation commutant is a formal power-series algebra

The constant coefficients of the outputs on divided monomials determine every
endomorphism commuting with differentiation. Their sequence is an arbitrary formal
series, and operator composition gives Cauchy convolution. This yields the full
algebra classification, with no continuity or convergence assumptions.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- The full algebra of polynomial endomorphisms commuting with differentiation. -/
def gomesPolynomialDerivativeCommutantAlgebra : Subalgebra K (Module.End K K[X]) :=
  Subalgebra.centralizer K {Polynomial.derivative}

/-- Actual polynomial differentiation symmetries. -/
abbrev GomesPolynomialDerivativeCommutant := ↥(gomesPolynomialDerivativeCommutantAlgebra K)

omit [CharZero K] in
/-- Algebra membership is precisely the actual differentiation commutation equation. -/
theorem gomesPolynomialDerivativeCommutant_mem_iff (E : Module.End K K[X]) :
    E ∈ gomesPolynomialDerivativeCommutantAlgebra K ↔
      E.comp Polynomial.derivative = Polynomial.derivative.comp E := by
  rw [gomesPolynomialDerivativeCommutantAlgebra, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h
    exact (h _ (Set.mem_singleton _)).symm
  · intro h F hF
    have hf : F = Polynomial.derivative := Set.mem_singleton_iff.mp hF
    rw [hf]
    exact h.symm

/-- A formal-series operator as an element of the actual differentiation commutant. -/
def gomesFormalSeriesCommutingOperator (F : PowerSeries K) : GomesPolynomialDerivativeCommutant K :=
  ⟨gomesFormalSeriesPolynomialOperator K F,
    (gomesPolynomialDerivativeCommutant_mem_iff K _).mpr
      (gomesFormalSeriesPolynomialOperator_commutes K F)⟩

/-- The formal symbol reads the constant term of each divided-monomial output. -/
def gomesDerivativeCommutantSymbol (E : GomesPolynomialDerivativeCommutant K) : PowerSeries K :=
  PowerSeries.mk fun n => (E.val (gomesDividedMonomialBasis K n)).coeff 0

/-- Each symbol coefficient is an actual polynomial output observation. -/
theorem gomesDerivativeCommutantSymbol_coeff (E : GomesPolynomialDerivativeCommutant K) (n : ℕ) :
    PowerSeries.coeff n (gomesDerivativeCommutantSymbol K E) =
      (E.val (gomesDividedMonomialBasis K n)).coeff 0 :=
  PowerSeries.coeff_mk n _

omit [CharZero K] in
/-- Commutation holds on every actual polynomial input. -/
theorem gomesDerivativeCommutant_apply_derivative
    (E : GomesPolynomialDerivativeCommutant K) (P : K[X]) :
    E.val P.derivative = (E.val P).derivative :=
  congrArg (fun F : Module.End K K[X] => F P)
    ((gomesPolynomialDerivativeCommutant_mem_iff K E.val).mp E.property)

/-- Constant outputs on divided monomials determine the entire commuting map. -/
theorem gomesPolynomialDerivativeCommutant_ext_iff
    (E F : GomesPolynomialDerivativeCommutant K) :
    E = F ↔ ∀ n : ℕ, (E.val (gomesDividedMonomialBasis K n)).coeff 0 =
      (F.val (gomesDividedMonomialBasis K n)).coeff 0 := by
  constructor
  · rintro rfl n
    rfl
  · intro h
    apply Subtype.ext
    apply (gomesDividedMonomialBasis K).ext
    intro n
    induction n with
    | zero =>
        apply (gomesPolynomial_derivative_coeff_zero_iff K _ _).mp
        refine ⟨?_, h 0⟩
        rw [← gomesDerivativeCommutant_apply_derivative K E,
          ← gomesDerivativeCommutant_apply_derivative K F,
          gomesDividedMonomialBasis_derivative_zero, map_zero, map_zero]
    | succ n ih =>
        apply (gomesPolynomial_derivative_coeff_zero_iff K _ _).mp
        refine ⟨?_, h (n + 1)⟩
        rw [← gomesDerivativeCommutant_apply_derivative K E,
          ← gomesDerivativeCommutant_apply_derivative K F,
          gomesDividedMonomialBasis_derivative_succ]
        exact ih

/-- Every formal coefficient sequence is recovered unchanged from its constructed operator. -/
theorem gomesDerivativeCommutantSymbol_formal_operator (F : PowerSeries K) :
    gomesDerivativeCommutantSymbol K (gomesFormalSeriesCommutingOperator K F) = F := by
  apply PowerSeries.ext
  intro n
  rw [gomesDerivativeCommutantSymbol_coeff]
  exact gomesFormalSeriesPolynomialOperator_coeff_zero K F n

/-- Every actual commuting map is reconstructed exactly from its formal symbol. -/
theorem gomesFormalSeriesCommutingOperator_symbol (E : GomesPolynomialDerivativeCommutant K) :
    gomesFormalSeriesCommutingOperator K (gomesDerivativeCommutantSymbol K E) = E := by
  apply (gomesPolynomialDerivativeCommutant_ext_iff K _ _).mpr
  intro n
  change (gomesFormalSeriesPolynomialOperator K (gomesDerivativeCommutantSymbol K E)
    (gomesDividedMonomialBasis K n)).coeff 0 = _
  rw [gomesFormalSeriesPolynomialOperator_coeff_zero, gomesDerivativeCommutantSymbol_coeff]

/-- The triangular coefficient expansion describes every actual commuting map. -/
theorem gomesPolynomialDerivativeCommutant_basis
    (E : GomesPolynomialDerivativeCommutant K) (n : ℕ) :
    E.val (gomesDividedMonomialBasis K n) =
      gomesFormalSeriesBasisImage K (gomesDerivativeCommutantSymbol K E) n := by
  have h := congrArg (fun F : GomesPolynomialDerivativeCommutant K =>
    F.val (gomesDividedMonomialBasis K n)) (gomesFormalSeriesCommutingOperator_symbol K E)
  change gomesFormalSeriesPolynomialOperator K (gomesDerivativeCommutantSymbol K E)
    (gomesDividedMonomialBasis K n) = _ at h
  rw [gomesFormalSeriesPolynomialOperator_basis] at h
  exact h.symm

/-- Composition of actual commuting maps is Cauchy multiplication of their formal symbols. -/
theorem gomesDerivativeCommutantSymbol_mul (E F : GomesPolynomialDerivativeCommutant K) :
    gomesDerivativeCommutantSymbol K (E * F) =
      gomesDerivativeCommutantSymbol K E * gomesDerivativeCommutantSymbol K F := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (gomesDerivativeCommutantSymbol K E) *
      PowerSeries.coeff j (gomesDerivativeCommutantSymbol K F)) n,
    gomesDerivativeCommutantSymbol_coeff]
  change (Polynomial.lcoeff K 0) (E.val (F.val (gomesDividedMonomialBasis K n))) = _
  rw [gomesPolynomialDerivativeCommutant_basis K F, gomesFormalSeriesBasisImage,
    map_sum, map_sum]
  simp only [map_smul]
  change (∑ j ∈ Finset.range (n + 1),
    PowerSeries.coeff (n - j) (gomesDerivativeCommutantSymbol K F) •
      (E.val (gomesDividedMonomialBasis K j)).coeff 0) = _
  simp only [gomesDerivativeCommutantSymbol_coeff, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- Addition of commuting maps is coefficientwise addition of their formal symbols. -/
theorem gomesDerivativeCommutantSymbol_add (E F : GomesPolynomialDerivativeCommutant K) :
    gomesDerivativeCommutantSymbol K (E + F) =
      gomesDerivativeCommutantSymbol K E + gomesDerivativeCommutantSymbol K F := by
  apply PowerSeries.ext
  intro n
  rw [map_add, gomesDerivativeCommutantSymbol_coeff, gomesDerivativeCommutantSymbol_coeff,
    gomesDerivativeCommutantSymbol_coeff]
  change (E.val (gomesDividedMonomialBasis K n) + F.val (gomesDividedMonomialBasis K n)).coeff 0 = _
  exact coeff_add _ _ _

/-- Scalar identity maps correspond to constant formal series. -/
theorem gomesDerivativeCommutantSymbol_algebraMap (c : K) :
    gomesDerivativeCommutantSymbol K (algebraMap K (GomesPolynomialDerivativeCommutant K) c) =
      algebraMap K (PowerSeries K) c := by
  apply PowerSeries.ext
  intro n
  rw [gomesDerivativeCommutantSymbol_coeff, PowerSeries.algebraMap_eq, PowerSeries.coeff_C]
  change (c • gomesDividedMonomialBasis K n).coeff 0 = _
  rw [coeff_smul, gomesDividedMonomialBasis_coeff_zero]
  by_cases h : n = 0 <;> simp [h]

/-- The full differentiation commutant is exactly the formal power-series algebra. -/
def gomesPolynomialDerivativeCommutantEquiv :
    GomesPolynomialDerivativeCommutant K ≃ₐ[K] PowerSeries K where
  toFun := gomesDerivativeCommutantSymbol K
  invFun := gomesFormalSeriesCommutingOperator K
  left_inv := gomesFormalSeriesCommutingOperator_symbol K
  right_inv := gomesDerivativeCommutantSymbol_formal_operator K
  map_mul' := gomesDerivativeCommutantSymbol_mul K
  map_add' := gomesDerivativeCommutantSymbol_add K
  commutes' := gomesDerivativeCommutantSymbol_algebraMap K

/-- A polynomial endomorphism commutes with differentiation exactly when it is one unique formal series. -/
theorem gomesPolynomialDerivative_commutes_iff_series (E : Module.End K K[X]) :
    (E.comp Polynomial.derivative = Polynomial.derivative.comp E) ↔
      ∃! F : PowerSeries K, E = gomesFormalSeriesPolynomialOperator K F := by
  constructor
  · intro h
    let e : GomesPolynomialDerivativeCommutant K :=
      ⟨E, (gomesPolynomialDerivativeCommutant_mem_iff K E).mpr h⟩
    have he := congrArg Subtype.val (gomesFormalSeriesCommutingOperator_symbol K e)
    refine ⟨gomesDerivativeCommutantSymbol K e, he.symm, ?_⟩
    intro F hF
    exact gomesFormalSeriesPolynomialOperator_injective K (hF.symm.trans he.symm)
  · rintro ⟨F, rfl, _⟩
    exact gomesFormalSeriesPolynomialOperator_commutes K F

/-- All endomorphisms commuting with polynomial differentiation commute with each other. -/
theorem gomesPolynomialDerivativeCommutant_commutative
    (E F : GomesPolynomialDerivativeCommutant K) : E * F = F * E := by
  apply (gomesPolynomialDerivativeCommutantEquiv K).injective
  rw [map_mul, map_mul, mul_comm]

end GaloisForLFunctions.HTGeometry

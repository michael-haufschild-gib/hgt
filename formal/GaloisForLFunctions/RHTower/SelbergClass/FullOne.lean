import GaloisForLFunctions.RHTower.SelbergClass.Full
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The degree-zero trivial full Selberg carrier

This module constructs the constant Dirichlet series `1` as a full Selberg-class carrier.  Its
coefficient arithmetic function is the delta function at `1`, its Euler logarithm is zero, and its
completed value has rank-zero gamma data and root number `1`.
-/

open scoped BigOperators
open Complex Filter Set

namespace RHTower

noncomputable section

/-- The constant entire function `1`, with a global finite-order growth witness. -/
def entireFiniteOrderOne : EntireFiniteOrder where
  toFun := fun _ => 1
  analytic := analyticOnNhd_const
  growth := by
    refine ⟨1, 1, 0, zero_lt_one, zero_lt_one, le_rfl, ?_⟩
    intro z
    rw [norm_one, Real.rpow_zero, one_mul, one_mul]
    exact Real.one_le_exp zero_le_one

@[simp]
theorem entireFiniteOrderOne_apply (s : ℂ) : entireFiniteOrderOne s = 1 :=
  rfl

/-- Pole-free continuation data representing the constant function `1`. -/
def selbergAnalyticContinuationOne : SelbergAnalyticContinuation where
  poleOrder := 0
  regularized := entireFiniteOrderOne

@[simp]
theorem selbergAnalyticContinuationOne_value (s : ℂ) :
    selbergAnalyticContinuationOne.value s = 1 := by
  simp [selbergAnalyticContinuationOne, SelbergAnalyticContinuation.value,
    entireFiniteOrderOne]

/-- Rank-zero gamma data for the trivial full Selberg carrier. -/
def selbergGammaDataOne : SelbergGammaData where
  Q := 1
  Q_pos := zero_lt_one
  rank := 0
  lambda := Fin.elim0
  lambda_pos := by
    intro j
    exact Fin.elim0 j
  mu := Fin.elim0
  mu_re_nonneg := by
    intro j
    exact Fin.elim0 j
  rootNumber := 1
  rootNumber_norm := by norm_num

@[simp]
theorem selbergGammaDataOne_rank : selbergGammaDataOne.rank = 0 :=
  rfl

@[simp]
theorem selbergGammaDataOne_rootNumber : selbergGammaDataOne.rootNumber = 1 :=
  rfl

@[simp]
theorem selbergGammaDataOne_gammaFactor (s : ℂ) :
    selbergGammaDataOne.gammaFactor s = 1 := by
  simp [selbergGammaDataOne, SelbergGammaData.gammaFactor]

/-- The degree-zero trivial object in the full Selberg carrier.  This declaration does not install
a `One` instance or assert any multiplication law for presentations. -/
noncomputable def SelbergClass.one : SelbergClass where
  coeff := 1
  coeff_ne_zero := by
    intro h
    have h1 := congrArg (fun f : ArithmeticFunction ℂ => f 1) h
    norm_num at h1
  lSeriesSummable := by
    intro s hs
    exact LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n _ => by
        by_cases h : n = 1 <;> simp [h]) hs
  continuation := selbergAnalyticContinuationOne
  lSeries_eq_value := by
    intro s hs
    change LSeries (fun n : ℕ => (1 : ArithmeticFunction ℂ) n) s =
      selbergAnalyticContinuationOne.value s
    calc
      LSeries (fun n : ℕ => (1 : ArithmeticFunction ℂ) n) s = LSeries LSeries.delta s := by
        rw [ArithmeticFunction.one_eq_delta]
      _ = 1 := by simpa using congrFun LSeries_delta s
      _ = selbergAnalyticContinuationOne.value s :=
        (selbergAnalyticContinuationOne_value s).symm
  gammaData := selbergGammaDataOne
  functionalEquation := by
    apply Filter.Eventually.of_forall
    intro s
    simp only [selbergCompletedValue, selbergGammaDataOne_gammaFactor,
      selbergAnalyticContinuationOne_value, selbergConjugateReflection]
    simp [selbergGammaDataOne]
  coeff_one := by simp
  ramanujan := by
    intro ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro n hn
    by_cases h : n = 1
    · subst n
      simp
    · rw [ArithmeticFunction.one_apply_ne h]
      simpa using (Real.rpow_nonneg (Nat.cast_nonneg n) ε)
  eulerLogCoeff := 0
  eulerLogCoeff_primePower := by simp
  eulerTheta := 0
  eulerTheta_lt_half := by norm_num
  eulerLogBound := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro n hn
    simp
  eulerLogSummable := by
    intro s hs
    exact LSeriesSummable_zero
  eulerProduct := by
    intro s hs
    change Complex.exp (LSeries (0 : ℕ → ℂ) s) =
      selbergAnalyticContinuationOne.value s
    simp [selbergAnalyticContinuationOne_value]

@[simp]
theorem SelbergClass.one_coeff : SelbergClass.one.coeff = 1 :=
  rfl

@[simp]
theorem SelbergClass.one_coeff_apply (n : ℕ) :
    SelbergClass.one.coeff n = if n = 1 then 1 else 0 :=
  ArithmeticFunction.one_apply

@[simp]
theorem SelbergClass.one_continuation_value (s : ℂ) :
    SelbergClass.one.continuation.value s = 1 :=
  selbergAnalyticContinuationOne_value s

@[simp]
theorem SelbergClass.one_gammaFactor (s : ℂ) :
    SelbergClass.one.gammaData.gammaFactor s = 1 :=
  selbergGammaDataOne_gammaFactor s

@[simp]
theorem SelbergClass.one_eulerLogCoeff : SelbergClass.one.eulerLogCoeff = 0 :=
  rfl

@[simp]
theorem SelbergClass.one_eulerLogCoeff_apply (n : ℕ) :
    SelbergClass.one.eulerLogCoeff n = 0 :=
  rfl

end

end RHTower

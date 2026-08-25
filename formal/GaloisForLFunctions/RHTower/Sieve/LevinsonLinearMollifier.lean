import GaloisForLFunctions.RHTower.Sieve.GrahamMeanSquare
import GaloisForLFunctions.RHTower.PrimeMassLowerBound
import GaloisForLFunctions.HTGeometry.TwistedDirichletMeanValue

/-!
# Linear Levinson mollifier

The linear choice `P(x) = x` has coefficient
`mu(n) n^(-1/2) log(M/n)/log M`.  It is packaged in the positive-natural `cdpoly` convention,
using the corpus's Barban--Vehov weight, with its exact formula and elementary `ell^1` bound.
-/

open Finset Complex ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.Sieve

/-- Positive-natural coefficient of the linear Levinson mollifier. -/
def levinsonLinearMollifierCoeff (M n : ℕ) : ℂ :=
  ((barbanVehovWeight M n / Real.log M : ℝ) : ℂ) *
    (((1 : ℝ) / Real.sqrt n : ℝ) : ℂ)

@[simp] theorem star_levinsonLinearMollifierCoeff (M n : ℕ) :
    (starRingEnd ℂ) (levinsonLinearMollifierCoeff M n) =
      levinsonLinearMollifierCoeff M n := by
  unfold levinsonLinearMollifierCoeff
  rw [map_mul, Complex.conj_ofReal, Complex.conj_ofReal]

/-- On its support this is exactly the usual
`mu(n) n^(-1/2) log(M/n)/log M` coefficient. -/
theorem levinsonLinearMollifierCoeff_eq
    {M n : ℕ} (hnM : n ≤ M) :
    levinsonLinearMollifierCoeff M n =
      ((((μ n : ℤ) : ℝ) * Real.log ((M : ℝ) / (n : ℝ)) /
          Real.log M : ℝ) : ℂ) *
        (((1 : ℝ) / Real.sqrt n : ℝ) : ℂ) := by
  rw [levinsonLinearMollifierCoeff, barbanVehovWeight, if_pos hnM]

/-- A linear mollifier coefficient is bounded by `n^(-1/2)`. -/
theorem norm_levinsonLinearMollifierCoeff_le
    {M n : ℕ} (hM : 1 < M) :
    ‖levinsonLinearMollifierCoeff M n‖ ≤ (1 : ℝ) / Real.sqrt n := by
  have hM1 : 1 ≤ M := Nat.le_of_lt hM
  have hlog : 0 < Real.log (M : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hM)
  have hw := abs_barbanVehovWeight_le (X := M) (m := n) hM1
  have hquot : |barbanVehovWeight M n| / Real.log M ≤ 1 := by
    exact (div_le_one hlog).2 hw
  rw [levinsonLinearMollifierCoeff, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs]
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / Real.sqrt n)]
  rw [abs_div, abs_of_pos hlog]
  exact mul_le_of_le_one_left (by positivity) hquot

/-- `ell^1` mass of the length-`M` linear mollifier. -/
theorem sum_norm_levinsonLinearMollifierCoeff_le
    {M : ℕ} (hM : 1 < M) :
    ∑ n ∈ Finset.Icc 1 M, ‖levinsonLinearMollifierCoeff M n‖ ≤
      2 * Real.sqrt M := by
  exact (Finset.sum_le_sum fun n hn =>
    norm_levinsonLinearMollifierCoeff_le hM).trans (RHTower.sum_one_div_sqrt_le M)

/-- Literal finite linear Levinson mollifier in the `cdpoly` convention. -/
def levinsonLinearMollifier (M : ℕ) (tau : ℝ) : ℂ :=
  cdpoly (levinsonLinearMollifierCoeff M) (Finset.Icc 1 M) 0 tau

theorem levinsonLinearMollifier_eq_sum
    (M : ℕ) (tau : ℝ) :
    levinsonLinearMollifier M tau =
      ∑ n ∈ Finset.Icc 1 M,
        levinsonLinearMollifierCoeff M n *
          Complex.exp (((-(Real.log n) * tau : ℝ) : ℂ) * I) := by
  rw [levinsonLinearMollifier, cdpoly]
  apply Finset.sum_congr rfl
  intro n hn
  simp [cdterm]

end RHTower.Sieve

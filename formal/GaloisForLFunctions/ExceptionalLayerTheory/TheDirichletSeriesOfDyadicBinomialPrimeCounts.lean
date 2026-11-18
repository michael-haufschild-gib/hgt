import GaloisForLFunctions.ExceptionalLayerTheory.ThePrimeCountInADyadicBinomialGcd
import GaloisForLFunctions.ExceptionalLayerTheory.TheLastQuotientClassDetectsEveryRightZero
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import GaloisForLFunctions.RHTower.Sieve.ConvolutionCoercion
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The Dirichlet series measured by dyadic binomial gcds

The prefix of the periodic jump sequence selects one quotient class.
Convolving the jumps with the actual prime weights identifies the count at
every cutoff. The mass between successive cutoffs is bounded by `log n`.
-/

noncomputable section

open Finset ArithmeticFunction Complex
open scoped LSeries.notation

namespace GaloisForLFunctions.ExceptionalLayerTheory

private def multipleIndicator (q n : ℕ) : ℝ := if q ∣ n then 1 else 0

/-- Jumps of the last quotient class as a real arithmetic function. -/
def lastClassCoefficients (q : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else multipleIndicator q (n+1) - multipleIndicator q n,by simp⟩

private theorem coeff_apply (q : ℕ) {n : ℕ} (hn : n ≠ 0) :
    lastClassCoefficients q n = multipleIndicator q (n+1) - multipleIndicator q n := if_neg hn

private theorem prefix_coeff (q : ℕ) (hq : 2 ≤ q) (X : ℕ) :
    ∑ n ∈ Icc 1 X, lastClassCoefficients q n = multipleIndicator q (X+1) := by
  induction X with
  | zero =>
    have h : ¬q ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
    simp [multipleIndicator,h]
  | succ X ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ X+1),ih,coeff_apply _ (Nat.succ_ne_zero X)]
    ring

/-- Every prefix of the jumps is either zero or one. -/
theorem lastClassCoefficients_prefix_bounds (q : ℕ) (hq : 2 ≤ q) (X : ℕ) :
    0 ≤ ∑ n ∈ Icc 1 X, lastClassCoefficients q n ∧
      ∑ n ∈ Icc 1 X, lastClassCoefficients q n ≤ 1 := by
  rw [prefix_coeff q hq]
  unfold multipleIndicator
  split <;> norm_num

/-- Logarithmic prime mass of the last quotient class at any integral cutoff. -/
def lastClassPrimeMass (q X : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 X, vonMangoldt m * multipleIndicator q (X/m+1)

/-- Coefficients of the Dirichlet series of this count. -/
def lastClassPrimeCoeff (q : ℕ) : ArithmeticFunction ℝ := vonMangoldt * lastClassCoefficients q

theorem lastClassPrimeMass_eq_prefix (q : ℕ) (hq : 2 ≤ q) (X : ℕ) :
    lastClassPrimeMass q X = ∑ n ∈ Icc 1 X, lastClassPrimeCoeff q n := by
  rw [lastClassPrimeCoeff,_root_.RHTower.sum_Icc_mul_apply]
  simp only [prefix_coeff q hq,lastClassPrimeMass]

theorem lastClassPrimeMass_at_dyadic (j N : ℕ) :
    lastClassPrimeMass (2^(j+1)) (2^(j+1)*N) = dyadicCommonPrimeMass j N := by
  unfold lastClassPrimeMass dyadicCommonPrimeMass
  refine sum_congr rfl fun m _ => ?_
  simp only [dyadicQuotientCarry,multipleIndicator]
  split <;> simp

/-- A single prime-count increment costs at most the sum of Mangoldt weights of the divisors. -/
theorem abs_lastClassPrimeCoeff_le (q n : ℕ) : |lastClassPrimeCoeff q n| ≤ Real.log n := by
  rw [lastClassPrimeCoeff,ArithmeticFunction.mul_apply]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ n.divisorsAntidiagonal, vonMangoldt d.1 := by
      refine sum_le_sum fun d _ => ?_
      rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
      apply mul_le_of_le_one_right vonMangoldt_nonneg
      by_cases h : d.2 = 0
      · simp [h]
      · rw [coeff_apply _ h]
        unfold multipleIndicator
        split_ifs <;> norm_num
    _ = _ := by rw [Nat.sum_divisorsAntidiagonal (fun a _ => (vonMangoldt a : ℝ)),vonMangoldt_sum]

/-- The bound between any two cutoffs is uniform in the modulus. -/
theorem lastClassPrimeMass_cutoff_gap {q M X : ℕ} (hq : 2 ≤ q) (hM : M ≤ X) :
    |lastClassPrimeMass q X - lastClassPrimeMass q M| ≤ (X-M : ℕ)*Real.log ((X:ℝ)+1) := by
  rw [lastClassPrimeMass_eq_prefix _ hq,lastClassPrimeMass_eq_prefix _ hq,
    ← Ico_add_one_right_eq_Icc 1 X,← Ico_add_one_right_eq_Icc 1 M,
    ← sum_Ico_consecutive (lastClassPrimeCoeff q) (by omega : 1 ≤ M+1) (by omega : M+1 ≤ X+1),
    add_sub_cancel_left]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _n ∈ Ico (M+1) (X+1), Real.log ((X:ℝ)+1) := by
      refine sum_le_sum fun n hn => (abs_lastClassPrimeCoeff_le q n).trans ?_
      have hn0 : 0 < n := by have := (mem_Ico.mp hn).1; omega
      apply Real.log_le_log (by exact_mod_cast hn0)
      exact_mod_cast (mem_Ico.mp hn).2.le
    _ = _ := by simp

private theorem cast_coeff {q n : ℕ} (hn : n ≠ 0) :
    (lastClassCoefficients q n : ℂ) = lastClassJumps (n : ZMod q) := by
  have h1 : ((n : ZMod q) = -1) ↔ q ∣ n+1 := by
    rw [← ZMod.natCast_eq_zero_iff,Nat.cast_add,Nat.cast_one,add_eq_zero_iff_eq_neg]
  rw [coeff_apply _ hn]
  simp [multipleIndicator,lastClassJumps,h1,ZMod.natCast_eq_zero_iff]
  split_ifs <;> simp

/-- Euler-half-plane factorization for the actual prime-count increments. -/
theorem lastClassPrimeCoeff_series (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (lastClassPrimeCoeff q n : ℂ)) s ∧
    LSeries (fun n => (lastClassPrimeCoeff q n : ℂ)) s =
      (-deriv riemannZeta s / riemannZeta s) * lastQuotientClassSymbol q s := by
  have hconv : (fun n => (lastClassPrimeCoeff q n : ℂ)) =
      ((fun n => (vonMangoldt n : ℂ)) ⍟ fun n => (lastClassCoefficients q n : ℂ)) := by
    funext n
    rw [LSeries.convolution_def]
    exact _root_.RHTower.Sieve.coe_mul_apply _ _ _
  have ha := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hb : LSeriesSummable (fun n => (lastClassCoefficients q n : ℂ)) s :=
    (LSeriesSummable_congr s cast_coeff).mpr (ZMod.LSeriesSummable_of_one_lt_re lastClassJumps hs)
  rw [hconv]
  refine ⟨ha.convolution hb,?_⟩
  rw [LSeries_convolution' ha hb,ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_congr cast_coeff s,lastQuotientClassSymbol_eq_LSeries q hs]

#print axioms lastClassPrimeMass_at_dyadic
#print axioms lastClassPrimeMass_cutoff_gap
#print axioms lastClassPrimeCoeff_series

end GaloisForLFunctions.ExceptionalLayerTheory

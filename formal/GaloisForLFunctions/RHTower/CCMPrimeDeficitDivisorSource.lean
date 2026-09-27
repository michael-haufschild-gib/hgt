import GaloisForLFunctions.RHTower.LogarithmicDivisorDilation
import GaloisForLFunctions.RHTower.CCMPrimeDeficitShortQuadraticWork

/-!
# The complete divisor source of the short quadratic reconstruction

The doubled dilation source is expressed solely through divisor counts,
reciprocal weights and logarithms. The same formula is an exact
divisor-weighted conservation identity for the full prime deficit.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitDivisorSource (T : ℝ) : ℝ :=
  Real.exp T * (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (n.divisors.card : ℝ) / n) -
    (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (n.divisors.card : ℝ)) -
      (1 / 2) * ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        (n.divisors.card : ℝ) * Real.log n * (T - Real.log n)

theorem ccmPrimeDeficitDilationSource_eq_elementary_dilations (T : ℝ) :
    ccmPrimeDeficitDilationSource T =
      logarithmicDilationSum (fun t => Real.exp t - 1) T -
        logarithmicWeightedDilation (fun n => Real.log n) (fun t => t) T := by
  unfold ccmPrimeDeficitDilationSource logarithmicDilationSum logarithmicWeightedDilation
  simp only [one_mul]
  congr 1
  have hcard : (⌊Real.exp T⌋₊ : ℝ) = ∑ _n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (1 : ℝ) := by
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rw [hcard, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [Real.exp_sub, Real.exp_log hnpos, div_eq_mul_inv]

/-- Every coefficient of the doubled source is elementary; no prime or
Möbius estimate is used to obtain this identity. -/
theorem logarithmicDilationSum_dilationSource_eq_divisorSource (T : ℝ) :
    logarithmicDilationSum ccmPrimeDeficitDilationSource T = ccmPrimeDeficitDivisorSource T := by
  have hg : ccmPrimeDeficitDilationSource = fun t =>
      logarithmicDilationSum (fun s => Real.exp s - 1) t -
        logarithmicWeightedDilation (fun n => Real.log n) (fun s => s) t :=
    funext ccmPrimeDeficitDilationSource_eq_elementary_dilations
  have hlin (f g : ℝ → ℝ) : logarithmicDilationSum (fun t => f t - g t) T =
      logarithmicDilationSum f T - logarithmicDilationSum g T := by
    simp only [logarithmicDilationSum, logarithmicWeightedDilation, mul_sub, Finset.sum_sub_distrib]
  rw [hg, hlin, logarithmicDilationSum_twice_eq_divisor_weighted,
    logarithmicDilationSum_log_weighted]
  unfold logarithmicWeightedDilation ccmPrimeDeficitDivisorSource
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [Real.exp_sub, Real.exp_log hnpos]
  ring

/-- Exact divisor-weighted conservation of the actual integrated prime
deficit, retaining every original delay and coefficient. -/
theorem ccmLogChebyshevDeficitPrimitive_divisor_dilation_conservation (T : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
      (n.divisors.card : ℝ) * ccmLogChebyshevDeficitPrimitive (T - Real.log n)) =
        ccmPrimeDeficitDivisorSource T := by
  have hg : logarithmicDilationSum ccmLogChebyshevDeficitPrimitive = ccmPrimeDeficitDilationSource := by
    funext t
    simpa only [logarithmicDilationSum, logarithmicWeightedDilation, one_mul] using
      ccmLogChebyshevDeficitPrimitive_dilation_conservation t
  have h := logarithmicDilationSum_twice_eq_divisor_weighted ccmLogChebyshevDeficitPrimitive T
  rw [hg, logarithmicDilationSum_dilationSource_eq_divisorSource] at h
  exact h.symm

/-- The full short quadratic form with the literal divisor source
inserted, preserving the actual Möbius signs and all main terms. -/
theorem ccmPrimeDeficitShortQuadraticWork_eq_divisorSource {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitShortQuadraticWork T = 2 * ccmPrimeDeficitShortMainWork T -
      ∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
          (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
            ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ)) := by
  rw [ccmPrimeDeficitShortQuadraticWork_eq_square hT]
  simp_rw [logarithmicDilationSum_dilationSource_eq_divisorSource]

end RHTower

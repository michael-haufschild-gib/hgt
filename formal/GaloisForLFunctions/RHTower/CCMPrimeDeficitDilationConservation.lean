import GaloisForLFunctions.RHTower.CCMPrimeDeficitPairEnergy
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap

/-!
# An arithmetic conservation law across multiplicative delays

Summing the literal integrated deficit at every delay `T-log(n)` removes
the prime coefficients exactly: each product fibre uses
`sum_{d | k} Lambda(d) = log(k)`. The resulting source is an elementary
finite logarithmic sum. Recovering the original deficit from this complete
sum requires signed inversion; no stability estimate is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

private theorem delayed_exp {T : ℝ} {n : ℕ} (hn : 0 < n) :
    Real.exp (T - Real.log n) = Real.exp T / n := by
  rw [Real.exp_sub, Real.exp_log (by exact_mod_cast hn)]

private theorem delayed_prefix (T : ℝ) {n : ℕ}
    (hn : n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) :
    ccmPrimeEntryPrefix ⌊Real.exp (T - Real.log n)⌋₊ (T - Real.log n) =
      ∑ m ∈ Finset.Icc 1 (⌊Real.exp T⌋₊ / n),
        ArithmeticFunction.vonMangoldt m * (T - Real.log ((n * m : ℕ) : ℝ)) := by
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [delayed_exp hnpos, Nat.floor_div_natCast, ccmPrimeEntryPrefix]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  have hprod : n * m ≤ ⌊Real.exp T⌋₊ := by
    have h := (Nat.le_div_iff_mul_le hnpos).mp (Finset.mem_Icc.mp hm).2
    simpa only [mul_comm] using h
  have hlog : Real.log ((n * m : ℕ) : ℝ) ≤ T :=
    (Real.log_le_iff_le_exp (by exact_mod_cast Nat.mul_pos hnpos hmpos)).mpr
      ((Nat.le_floor_iff (Real.exp_pos T).le).mp hprod)
  have hsplit : Real.log ((n * m : ℕ) : ℝ) = Real.log n + Real.log m := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast Nat.ne_of_gt hnpos)
      (by exact_mod_cast Nat.ne_of_gt hmpos)]
  rw [hsplit] at hlog ⊢
  rw [ccmPrimeEntryTent, max_eq_left (by linarith)]
  ring

/-- Complete multiplicative-delay summation replaces the prime-entry
weights by the exact divisor logarithm. -/
theorem ccmPrimeEntryPrefix_dilation_conservation (T : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
      ccmPrimeEntryPrefix ⌊Real.exp (T - Real.log n)⌋₊ (T - Real.log n)) =
        ∑ k ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, Real.log k * (T - Real.log k) := by
  rw [Finset.sum_congr rfl (fun n hn => delayed_prefix T hn),
    ← Sieve.sum_Icc_divisorsAntidiagonal_swap]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ x ∈ k.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt x.2 * (T - Real.log k) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    _ = _ := by
      rw [← Finset.sum_mul, Nat.sum_divisorsAntidiagonal'
        (fun _ m => ArithmeticFunction.vonMangoldt m), ArithmeticFunction.vonMangoldt_sum]

def ccmPrimeDeficitDilationSource (T : ℝ) : ℝ :=
  Real.exp T * (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (n : ℝ)⁻¹) -
    (⌊Real.exp T⌋₊ : ℝ) -
      ∑ k ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, Real.log k * (T - Real.log k)

/-- The actual signed deficit satisfies this unconditional arithmetic
conservation identity at every real logarithmic time. -/
theorem ccmLogChebyshevDeficitPrimitive_dilation_conservation (T : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
      ccmLogChebyshevDeficitPrimitive (T - Real.log n)) = ccmPrimeDeficitDilationSource T := by
  have hp (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) :
      ccmLogChebyshevDeficitPrimitive (T - Real.log n) =
        Real.exp T / n - 1 -
          ccmPrimeEntryPrefix ⌊Real.exp (T - Real.log n)⌋₊ (T - Real.log n) := by
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hlog : Real.log n ≤ T :=
      (Real.log_le_iff_le_exp (by exact_mod_cast hnpos)).mpr
        ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2)
    rw [ccmLogChebyshevDeficitPrimitive_eq_entry_prefix (sub_nonneg.mpr hlog) le_rfl,
      delayed_exp hnpos]
  rw [Finset.sum_congr rfl hp]
  simp only [Finset.sum_sub_distrib, ccmPrimeEntryPrefix_dilation_conservation,
    div_eq_mul_inv, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rfl

end RHTower

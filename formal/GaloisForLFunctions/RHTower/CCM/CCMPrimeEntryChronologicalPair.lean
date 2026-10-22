import GaloisForLFunctions.RHTower.CCM.CCMPrimeEntryPairBoundary
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitWeilFlux

/-!
# Chronological ordering of the complete prime-pair interaction

Ordering the symmetric pair sum by its later prime entry makes every
interaction depend on the arithmetic state at that entry. The diagonal
correction is the harmonic von Mangoldt square sum. The work below uses
the left value of psi, including prime powers without exception.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeEntryPrejumpWork (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) *
    (ccmLogChebyshevDeficitPrimitive (Real.log n) +
      2 * ((n : ℝ) - Chebyshev.psi n + ArithmeticFunction.vonMangoldt n))

private theorem symmetric_square_sum (f : ℕ → ℕ → ℝ)
    (hf : ∀ n m, f n m = f m n) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, f n m) =
      2 * (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 n, f n m) -
        ∑ n ∈ Finset.Icc 1 N, f n n := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
    simp only [Finset.sum_Icc_succ_top hN, Finset.sum_add_distrib]
    rw [ih]
    have hcol : (∑ n ∈ Finset.Icc 1 N, f n (N + 1)) =
        ∑ n ∈ Finset.Icc 1 N, f (N + 1) n :=
      Finset.sum_congr rfl (fun n _ => hf n (N + 1))
    rw [hcol]
    ring

private theorem psi_nat_eq (N : ℕ) :
    Chebyshev.psi N = ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n := by
  simp only [Chebyshev.psi, Nat.floor_natCast, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

/-- The complete limiting pair sum is twice its chronological triangle,
with precisely one copy of each self-interaction removed. -/
theorem ccmPrimeEntryPairLimit_eq_chronological (N : ℕ) :
    ccmPrimeEntryPairLimit N =
      2 * (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) *
        (ccmPrimeEntryPrefix n (Real.log n) + 2 * Chebyshev.psi n)) -
      2 * ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2 / (n : ℝ) := by
  let f : ℕ → ℕ → ℝ := fun n m =>
    ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m *
      ccmPrimeEntryOverlapLimit (Real.log n) (Real.log m)
  have hf (n m : ℕ) : f n m = f m n := by
    dsimp only [f]
    rw [ccmPrimeEntryOverlapLimit_comm (Real.log n) (Real.log m)]
    ring
  have hrow (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (∑ m ∈ Finset.Icc 1 n, f n m) =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) *
          (ccmPrimeEntryPrefix n (Real.log n) + 2 * Chebyshev.psi n) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [ccmPrimeEntryPrefix, psi_nat_eq, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmn : Real.log m ≤ Real.log n :=
      Real.log_le_log hmpos (by exact_mod_cast (Finset.mem_Icc.mp hm).2)
    dsimp only [f]
    rw [ccmPrimeEntryOverlapLimit, max_eq_left hmn,
      abs_of_nonneg (sub_nonneg.mpr hmn), Real.exp_neg, Real.exp_log hnpos,
      ccmPrimeEntryTent, max_eq_left (sub_nonneg.mpr hmn)]
    ring
  have hdiag : (∑ n ∈ Finset.Icc 1 N, f n n) =
      2 * ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2 / (n : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [f]
    rw [ccmPrimeEntryOverlapLimit_log_self (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)]
    ring
  exact (symmetric_square_sum f hf N).trans (by
    rw [Finset.sum_congr rfl hrow, hdiag])

/-- Replacing each entry prefix by its literal deficit leaves a signed
prejump work and the harmonic square correction. -/
theorem ccmPrimeEntryPairLimit_eq_prejumpWork (N : ℕ) :
    ccmPrimeEntryPairLimit N = -2 * ccmPrimeEntryPrejumpWork N +
      2 * (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2 / (n : ℝ)) +
        6 * Chebyshev.psi N - 2 * mertensSum N := by
  rw [ccmPrimeEntryPairLimit_eq_chronological, ccmPrimeEntryPrejumpWork,
    psi_nat_eq, mertensSum]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hnpos := zero_lt_one.trans_le hn1
  have hD := ccmLogChebyshevDeficitPrimitive_eq_entry_prefix
    (N := n) (Real.log_nonneg hn1) (by rw [Real.exp_log hnpos, Nat.floor_natCast])
  rw [Real.exp_log hnpos] at hD
  rw [hD]
  field_simp
  ring

end RHTower

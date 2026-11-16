import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.IntegerNormFakesAboveOneHalf
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Primitive necklace counts with an explicit error

Möbius inversion identifies the primitive-word count with a divisor sum.
Splitting off the full-length divisor and bounding all proper divisors by
half the length gives a finite version of the exponential-growth argument
in Zehavi, Proposition 4.5, arXiv:2611.18218.
-/

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

open Finset ArithmeticFunction

/-- The existing orbit count is the integral Möbius transform of the full word count. -/
theorem mul_necklaceCount_eq_moebius (a n : ℕ) :
    ((n + 1 : ℕ) : ℤ) * (necklaceCount a (n + 1) : ℤ) =
      ∑ d ∈ (n + 1).divisors, moebius ((n + 1) / d) * (a : ℤ) ^ d := by
  have hsum (m : ℕ) (hm : 0 < m) :
      (∑ d ∈ m.divisors, (d : ℤ) * (necklaceCount a d : ℤ)) = (a : ℤ) ^ m := by
    exact_mod_cast sum_divisors_mul_necklaceCount a hm
  have h := (sum_eq_iff_sum_mul_moebius_eq.mp hsum) (n + 1) (Nat.succ_pos n)
  simp only [Int.cast_id] at h
  rw [Nat.sum_divisorsAntidiagonal' (fun i j => (moebius i : ℤ) * (a : ℤ) ^ j)] at h
  exact h.symm

/-- Every discrepancy from the leading word count comes from shorter primitive orbits. -/
theorem necklaceCount_main_term_error (a n : ℕ) :
    a ^ (n + 1) - (n + 1) * necklaceCount a (n + 1) =
      ∑ d ∈ (n + 1).properDivisors, d * necklaceCount a d := by
  have h := sum_divisors_mul_necklaceCount a (Nat.succ_pos n)
  rw [← Nat.cons_self_properDivisors (Nat.succ_ne_zero n), Finset.sum_cons] at h
  change (n + 1) * necklaceCount a (n + 1) +
    ∑ d ∈ (n + 1).properDivisors, d * necklaceCount a d = a ^ (n + 1) at h
  omega

private theorem properDivisor_mem_half {n d : ℕ} (hd : d ∈ (n + 1).properDivisors) :
    d ∈ Finset.Icc 1 ((n + 1) / 2) := by
  have hpos := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hd).1 (Nat.succ_pos n)
  obtain ⟨k, hk, he⟩ := (Nat.mem_properDivisors_iff_exists (Nat.succ_ne_zero n)).mp hd
  change n + 1 = d * k at he
  have hmul : d * 2 ≤ n + 1 := by
    rw [he]
    exact Nat.mul_le_mul_left d hk
  exact Finset.mem_Icc.mpr ⟨hpos, (Nat.le_div_iff_mul_le (by decide)).mpr hmul⟩

/-- The nonprimitive part is bounded by all word counts up to half the length. -/
theorem necklaceCount_error_le_half_sum (a n : ℕ) :
    a ^ (n + 1) - (n + 1) * necklaceCount a (n + 1) ≤
      ∑ d ∈ Finset.Icc 1 ((n + 1) / 2), a ^ d := by
  rw [necklaceCount_main_term_error]
  calc
    _ ≤ ∑ d ∈ (n + 1).properDivisors, a ^ d := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_necklaceCount_le_pow a d (Finset.mem_Icc.mp (properDivisor_mem_half hd)).1
    _ ≤ _ := Finset.sum_le_sum_of_subset fun _ hd => properDivisor_mem_half hd

/-- An unconditional exponential error bound, also covering empty and singleton alphabets. -/
theorem necklaceCount_error_le_half_pow (a n : ℕ) :
    a ^ (n + 1) - (n + 1) * necklaceCount a (n + 1) ≤
      ((n + 1) / 2) * (max a 1) ^ ((n + 1) / 2) := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ((n + 1) / 2), a ^ d := necklaceCount_error_le_half_sum a n
    _ ≤ ∑ _d ∈ Finset.Icc 1 ((n + 1) / 2), (max a 1) ^ ((n + 1) / 2) := by
      apply Finset.sum_le_sum
      intro d hd
      exact (Nat.pow_le_pow_left (le_max_left a 1) d).trans
        (Nat.pow_le_pow_right (lt_of_lt_of_le Nat.zero_lt_one (le_max_right a 1))
          (Finset.mem_Icc.mp hd).2)
    _ = _ := by simp [Nat.card_Icc]

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

#print axioms GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.mul_necklaceCount_eq_moebius
#print axioms GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.necklaceCount_main_term_error
#print axioms GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.necklaceCount_error_le_half_pow

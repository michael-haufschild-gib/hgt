import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples

/-!
# On average a number has boundedly many balanced divisors

Exchanging the order of summation, the total number of divisors in a window `[y, 2y]` over all
`m ≤ X` is a sum of multiple-counts:

`∑_{m ≤ X} #{d ∣ m : y ≤ d ≤ 2y} = ∑_{y ≤ d ≤ 2y} ⌊X/d⌋ ≤ X ∑_{y ≤ d ≤ 2y} 1/d`,

and the last sum is bounded (it is `≈ log 2`).  So although a single integer can have `2^{ω(m)}`
coprime factorizations — unbounded, as `card_divisors_of_squarefree` records — the *average* number
of balanced ones is `O(1)`.

The multiplicity obstruction is therefore pointwise but not on average, which is the distinction the
coprime card's hard gate turns on.
-/

namespace RHTower.Sieve

open Finset

/-- **The balanced divisor count, summed over `m ≤ X`.** -/
theorem sum_card_divisors_window_le (X y : ℕ) :
    ∑ m ∈ Finset.Icc 1 X, ((((Finset.Icc y (2 * y)).filter (fun d => d ∣ m)).card : ℕ) : ℝ)
      ≤ (X : ℝ) * ∑ d ∈ Finset.Icc y (2 * y), 1 / (d : ℝ) := by
  classical
  have hIcc : Finset.Icc 1 X = Finset.Ioc 0 X := by
    ext x
    simp [Nat.lt_iff_add_one_le]
  have hcount : ∀ m : ℕ,
      ((((Finset.Icc y (2 * y)).filter (fun d => d ∣ m)).card : ℕ) : ℝ)
        = ∑ d ∈ Finset.Icc y (2 * y), (if d ∣ m then (1 : ℝ) else 0) := by
    intro m
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun m _ => hcount m, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · have hzero : ∑ m ∈ Finset.Icc 1 X, (if (0 : ℕ) ∣ m then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.mem_Icc] at hm
      rw [if_neg]
      intro hdvd
      have := Nat.eq_zero_of_zero_dvd hdvd
      omega
    rw [hzero]
    simp
  · have hinner : ∑ m ∈ Finset.Icc 1 X, (if d ∣ m then (1 : ℝ) else 0)
        = (((X / d : ℕ) : ℕ) : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hIcc]
      congr 1
      exact Nat.Ioc_filter_dvd_card_eq_div X d
    rw [hinner]
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hdiv : (((X / d : ℕ) : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hdR]
      have := Nat.div_mul_le_self X d
      exact_mod_cast this
    calc (((X / d : ℕ) : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) := hdiv
      _ = (X : ℝ) * (1 / (d : ℝ)) := by ring

/-- The reciprocal sum over a dyadic window is at most `2`. -/
theorem sum_inv_window_le_two {y : ℕ} (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc y (2 * y), 1 / (d : ℝ) ≤ 2 := by
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hterm : ∀ d ∈ Finset.Icc y (2 * y), 1 / (d : ℝ) ≤ 1 / (y : ℝ) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdR : (y : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
    exact one_div_le_one_div_of_le (by linarith) hdR
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hcard : ((2 * y + 1 - y : ℕ) : ℝ) = (y : ℝ) + 1 := by
    have : 2 * y + 1 - y = y + 1 := by omega
    rw [this]
    push_cast
    ring
  rw [hcard]
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  rw [mul_one_div, div_le_iff₀ hypos]
  linarith

/-- **On average a number has at most two balanced divisors.** -/
theorem sum_card_divisors_window_le_two (X : ℕ) {y : ℕ} (hy : 1 ≤ y) :
    ∑ m ∈ Finset.Icc 1 X, ((((Finset.Icc y (2 * y)).filter (fun d => d ∣ m)).card : ℕ) : ℝ)
      ≤ 2 * (X : ℝ) := by
  refine le_trans (sum_card_divisors_window_le X y) ?_
  have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hsum := sum_inv_window_le_two hy
  calc (X : ℝ) * ∑ d ∈ Finset.Icc y (2 * y), 1 / (d : ℝ)
      ≤ (X : ℝ) * 2 := mul_le_mul_of_nonneg_left hsum hX
    _ = 2 * (X : ℝ) := by ring

end RHTower.Sieve

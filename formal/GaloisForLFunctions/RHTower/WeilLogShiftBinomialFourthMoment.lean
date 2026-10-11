import GaloisForLFunctions.RHTower.WeilLogShiftBinomialSecondMoment

/-! Exact fourth moments obtained from the same Pascal recurrence as the second moments. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeil_binomial_centered_fourth_moment (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (2 * (i : ℝ) - (n : ℝ)) ^ 4) =
      (3 * (n : ℝ) ^ 2 - 2 * n) * (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmass : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    have hsplit := Finset.sum_choose_succ_mul (R := ℝ)
      (fun i _ => (2 * (i : ℝ) - ((n + 1 : ℕ) : ℝ)) ^ 4) n
    calc
      _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            (2 * (i : ℝ) - ((n + 1 : ℕ) : ℝ)) ^ 4) +
          ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            (2 * ((i + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) ^ 4 := hsplit
      _ = 2 * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (2 * (i : ℝ) - (n : ℝ)) ^ 4) +
          12 * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (2 * (i : ℝ) - (n : ℝ)) ^ 2) +
          2 * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        push_cast
        ring
      _ = _ := by
        rw [ih, finiteWeil_binomial_centered_second_moment, hmass, pow_succ]
        push_cast
        ring

theorem finiteWeil_binomial_half_centered_fourth_moment (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((i : ℝ) - (n : ℝ) / 2) ^ 4) =
      ((3 * (n : ℝ) ^ 2 - 2 * n) / 16) * (2 : ℝ) ^ n := by
  have h := finiteWeil_binomial_centered_fourth_moment n
  have heq :
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (2 * (i : ℝ) - (n : ℝ)) ^ 4) =
        16 * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((i : ℝ) - (n : ℝ) / 2) ^ 4 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq] at h
  nlinarith only [h]

end RHTower

import GaloisForLFunctions.RHTower.WeilLogShiftBinomialSecondMoment

/-! Exact mass, mean and centered second moment of the arithmetic binomial probability. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeil_binomial_first_moment (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (i : ℝ)) =
      (n : ℝ) / 2 * (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmass : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    have hsplit := Finset.sum_choose_succ_mul (R := ℝ) (fun i _ => (i : ℝ)) n
    calc
      _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (i : ℝ)) +
          ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((i + 1 : ℕ) : ℝ) := hsplit
      _ = 2 * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (i : ℝ)) +
          ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        push_cast
        ring
      _ = _ := by rw [ih, hmass, pow_succ]; push_cast; ring

theorem finiteWeil_binomial_probability_mass (r : ℕ) :
    (∑ u : Fin (r + 2), ((r + 1).choose (u : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) = 1 := by
  rw [← Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => ((r + 1).choose i : ℝ)) (r + 2)]
  have hm : (∑ i ∈ Finset.range ((r + 1) + 1), ((r + 1).choose i : ℝ)) =
      (2 : ℝ) ^ (r + 1) := by exact_mod_cast Nat.sum_range_choose (r + 1)
  rw [hm]
  have hp : (2 : ℝ) ^ (r + 1) ≠ 0 := by positivity
  exact div_self hp

theorem finiteWeil_binomial_probability_mean (r : ℕ) :
    (∑ u : Fin (r + 2), (((r + 1).choose (u : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) * ((u : ℕ) : ℝ)) =
      ((r + 1 : ℕ) : ℝ) / 2 := by
  have hs : (∑ u : Fin (r + 2), (((r + 1).choose (u : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) * ((u : ℕ) : ℝ)) =
      (∑ u : Fin (r + 2), ((r + 1).choose (u : ℕ) : ℝ) * ((u : ℕ) : ℝ)) / (2 : ℝ) ^ (r + 1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hs, Fin.sum_univ_eq_sum_range (fun i : ℕ => ((r + 1).choose i : ℝ) * (i : ℝ)) (r + 2),
    finiteWeil_binomial_first_moment]
  have hp : (2 : ℝ) ^ (r + 1) ≠ 0 := by positivity
  field_simp

theorem finiteWeil_binomial_probability_centered_second_moment (r : ℕ) :
    (∑ u : Fin (r + 2), (((r + 1).choose (u : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) *
      (((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) = ((r + 1 : ℕ) : ℝ) / 4 := by
  have hs : (∑ u : Fin (r + 2), (((r + 1).choose (u : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) *
      (((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) =
      (∑ u : Fin (r + 2), ((r + 1).choose (u : ℕ) : ℝ) *
        (((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) / (2 : ℝ) ^ (r + 1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hs, Fin.sum_univ_eq_sum_range (fun i : ℕ => ((r + 1).choose i : ℝ) *
      ((i : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) (r + 2), finiteWeil_binomial_half_centered_second_moment]
  have hp : (2 : ℝ) ^ (r + 1) ≠ 0 := by positivity
  field_simp

end RHTower

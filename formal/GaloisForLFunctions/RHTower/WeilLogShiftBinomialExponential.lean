import GaloisForLFunctions.HTGeometry.BinomialTailBetaThreshold

/-! Centered binomial exponential moments at the finite Weil fluctuation scale. -/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeil_binomialTerm_half (n : ℕ) (j : Fin (n + 1)) :
    binomialTerm n j (1 / 2) = (n.choose (j : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  have hj : (j : ℕ) + (n - j) = n := by omega
  unfold binomialTerm
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  calc
    _ = (n.choose (j : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ (j : ℕ) * (1 / 2 : ℝ) ^ (n - j)) := by ring
    _ = _ := by rw [← pow_add, hj]; simp only [div_pow, one_pow, mul_one_div]

theorem finiteWeil_binomial_centered_exponential_bound (n : ℕ) (a : ℝ) :
    (∑ j : Fin (n + 1), ((n.choose (j : ℕ) : ℝ) / (2 : ℝ) ^ n) *
      Real.exp (a * ((j : ℝ) - (n : ℝ) / 2))) ≤ Real.exp ((n : ℝ) * a ^ 2 / 8) := by
  have h := sum_binomialTerm_mul_exp_le (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) n a
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => binomialTerm n j (1 / 2) * Real.exp (a * j)) (n + 1)] at h
  calc
    _ = Real.exp (-a * (n : ℝ) / 2) *
        ∑ j : Fin (n + 1), binomialTerm n j (1 / 2) * Real.exp (a * j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [finiteWeil_binomialTerm_half]
      have he : a * ((j : ℝ) - (n : ℝ) / 2) = -a * (n : ℝ) / 2 + a * j := by ring
      rw [he, Real.exp_add]
      ring
    _ ≤ Real.exp (-a * (n : ℝ) / 2) * Real.exp ((n : ℝ) * (a * (1 / 2) + a ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem finiteWeil_binomial_scaled_exponential_bound (r : ℕ) (a : ℝ) :
    (∑ j : Fin (r + 2), (((r + 1).choose (j : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) *
      Real.exp (a * ((j : ℝ) - (r + 1 : ℕ) / 2) / Real.sqrt (r + 1 : ℕ))) ≤
      Real.exp (a ^ 2 / 8) := by
  have h := finiteWeil_binomial_centered_exponential_bound (r + 1)
    (a / Real.sqrt (r + 1 : ℕ))
  have hn : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have he : ((r + 1 : ℕ) : ℝ) * (a / Real.sqrt (r + 1 : ℕ)) ^ 2 / 8 = a ^ 2 / 8 := by
    rw [div_pow, Real.sq_sqrt hn.le]
    field_simp
  rw [he] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  ring

end RHTower

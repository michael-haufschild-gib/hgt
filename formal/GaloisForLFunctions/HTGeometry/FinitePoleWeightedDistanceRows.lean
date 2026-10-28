import GaloisForLFunctions.HTGeometry.FiniteInverseSquareDistanceRows

/-!
# Pole-weighted inverse-square rows

Near the row index, the pole weights are comparable and the reciprocal-square
sum is bounded. Away from it, the difference is comparable to the larger index.
This yields a square-root row bound suitable for Euclidean residual estimates.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

private theorem pole_weighted_distance_term_le {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    (max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2) ≤
      8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 + 4 := by
  by_cases hnj : n = j
  · subst j
    simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
  have hsj1 : 1 ≤ Real.sqrt (j : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hjR
  have hsnsq := Real.sq_sqrt hn0.le
  have hsjsq := Real.sq_sqrt hj0.le
  have hd : 0 < |(n : ℝ) - j| := by
    rw [abs_pos, sub_ne_zero]
    exact_mod_cast hnj
  have hd2 := sq_pos_of_pos hd
  have hm0 : 0 ≤ max (n : ℝ) j := hn0.le.trans (le_max_left _ _)
  by_cases hnear : n ≤ 2 * j ∧ j ≤ 2 * n
  · have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnear.1
    have hjnR : (j : ℝ) ≤ 2 * n := by exact_mod_cast hnear.2
    have hs : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (j : ℝ) := by
      by_contra h
      have hlt : 2 * Real.sqrt (j : ℝ) < Real.sqrt (n : ℝ) := lt_of_not_ge h
      have hp := mul_pos (sub_pos.mpr hlt) (by positivity :
        0 < Real.sqrt (n : ℝ) + 2 * Real.sqrt (j : ℝ))
      nlinarith only [hp, hsnsq, hsjsq, hnjR, hj0]
    have hm : max (n : ℝ) j ≤ 2 * n := max_le (by linarith only [hn0]) hjnR
    have hm2 : (max (n : ℝ) j) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
      have hsq := mul_self_le_mul_self hm0 hm
      nlinarith only [hsq]
    have hnum : (max (n : ℝ) j) ^ 2 ≤ 8 * (n : ℝ) * Real.sqrt n * Real.sqrt j := by
      calc
        _ ≤ 4 * (n : ℝ) ^ 2 := hm2
        _ = (4 * (n : ℝ) * Real.sqrt n) * Real.sqrt n := by
          rw [mul_assoc (4 * (n : ℝ)), ← pow_two, hsnsq]
          ring
        _ ≤ (4 * (n : ℝ) * Real.sqrt n) * (2 * Real.sqrt j) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by ring
    have hterm : (max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2) ≤
        8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos hsj hd2) hd2]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hnum) hd2.le]
    exact hterm.trans (le_add_of_nonneg_right (by norm_num))
  · have hm : max (n : ℝ) j ≤ 2 * |(n : ℝ) - j| := by
      rcases not_and_or.mp hnear with h | h
      · have hnR' : 2 * (j : ℝ) < n := by exact_mod_cast (lt_of_not_ge h)
        rw [max_eq_left (by linarith only [hnR', hj0]),
          abs_of_pos (by linarith only [hnR', hj0])]
        linarith only [hnR']
      · have hjR' : 2 * (n : ℝ) < j := by exact_mod_cast (lt_of_not_ge h)
        rw [max_eq_right (by linarith only [hjR', hn0]),
          abs_of_neg (by linarith only [hjR', hn0])]
        linarith only [hjR']
    have hm2 : (max (n : ℝ) j) ^ 2 ≤ 4 * |(n : ℝ) - j| ^ 2 := by
      have hsq := mul_self_le_mul_self hm0 hm
      nlinarith only [hsq]
    have hterm : (max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2) ≤ 4 := by
      rw [div_le_iff₀ (mul_pos hsj hd2)]
      nlinarith only [hm2, mul_nonneg (sub_nonneg.mpr hsj1) hd2.le]
    exact hterm.trans (le_add_of_nonneg_left (by positivity))

/-- A pole-weighted distance row is at most a fixed multiple of `N sqrt(n)`. -/
theorem sum_pole_weighted_distance_row_le {n N : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ Icc 1 N,
      (max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2)) ≤
      36 * (N : ℝ) * Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  have hsn1 : 1 ≤ Real.sqrt (n : ℝ) := by
    have h : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt h
  have hsum := sum_inv_sq_integer_distance_le_four (Icc 1 N) n
  calc
    _ ≤ ∑ j ∈ Icc 1 N,
        (8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 + 4) :=
      sum_le_sum fun j hj => pole_weighted_distance_term_le (mem_Icc.mp hn).1 (mem_Icc.mp hj).1
    _ = 8 * (n : ℝ) * Real.sqrt n * (∑ j ∈ Icc 1 N, 1 / |(n : ℝ) - j| ^ 2) +
        4 * (N : ℝ) := by
      simp only [sum_add_distrib, div_eq_mul_inv, ← mul_sum, sum_const, Nat.card_Icc,
        Nat.add_sub_cancel, nsmul_eq_mul, one_mul]
      ring
    _ ≤ 32 * (n : ℝ) * Real.sqrt n + 4 * (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 8 * (n : ℝ) * Real.sqrt n by positivity)
      nlinarith only [h]
    _ ≤ 36 * (N : ℝ) * Real.sqrt n := by
      have h1 := mul_le_mul_of_nonneg_right hnN (show 0 ≤ 32 * Real.sqrt (n : ℝ) by positivity)
      have h2 := mul_le_mul_of_nonneg_left hsn1 (show 0 ≤ 4 * (N : ℝ) by positivity)
      nlinarith only [h1, h2]

end GaloisForLFunctions.HTGeometry

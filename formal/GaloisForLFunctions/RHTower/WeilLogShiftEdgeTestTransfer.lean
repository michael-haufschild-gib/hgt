import GaloisForLFunctions.RHTower.WeilLogShiftEdgeMidpoint

/-! Stable test-function transfer from the midpoint probability to its edge probability. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilCanonicalMixture_midpoint_edge_difference (r k : ℕ) (f : Fin (r + 2) → ℝ) :
    (∑ u, finiteWeilCanonicalMixture r k (1 / 2) u * f u) -
      (∑ i, finiteWeilCanonicalEdgeMass r k i * f i.castSucc) =
      (∑ i, finiteWeilCanonicalEdgeMass r k i * (f i.succ - f i.castSucc)) / 2 := by
  rw [finiteWeilCanonicalMixture_midpoint_edge_pairing]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem finiteWeilCanonicalMixture_midpoint_edge_test_bound (r k : ℕ) (f : Fin (r + 2) → ℝ)
    (L : ℝ) (hstep : ∀ i : Fin (r + 1), |f i.succ - f i.castSucc| ≤ L) :
    |(∑ u, finiteWeilCanonicalMixture r k (1 / 2) u * f u) -
      (∑ i, finiteWeilCanonicalEdgeMass r k i * f i.castSucc)| ≤ L / 2 := by
  have hs : |∑ i, finiteWeilCanonicalEdgeMass r k i * (f i.succ - f i.castSucc)| ≤ L := by
    calc
      _ ≤ ∑ i, |finiteWeilCanonicalEdgeMass r k i * (f i.succ - f i.castSucc)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, finiteWeilCanonicalEdgeMass r k i * |f i.succ - f i.castSucc| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (le_of_lt (finiteWeilCanonicalEdgeMass_pos r k i))]
      _ ≤ ∑ i, finiteWeilCanonicalEdgeMass r k i * L :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hstep i)
          (le_of_lt (finiteWeilCanonicalEdgeMass_pos r k i))
      _ = L := by rw [← Finset.sum_mul, finiteWeilCanonicalEdgeMass_sum, one_mul]
  rw [finiteWeilCanonicalMixture_midpoint_edge_difference, abs_div]
  norm_num
  linarith only [hs]

theorem finiteWeil_profile_test_l1_bound {ι : Type*} [Fintype ι] (P Q f : ι → ℝ)
    (C : ℝ) (hf : ∀ u, |f u| ≤ C) :
    |(∑ u, P u * f u) - (∑ u, Q u * f u)| ≤ C * ∑ u, |P u - Q u| := by
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  calc
    _ ≤ ∑ u, |(P u - Q u) * f u| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ u, |P u - Q u| * |f u| := by simp only [abs_mul]
    _ ≤ ∑ u, |P u - Q u| * C :=
      Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hf u) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

end RHTower

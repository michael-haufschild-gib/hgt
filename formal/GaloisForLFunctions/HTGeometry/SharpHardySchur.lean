import GaloisForLFunctions.HTGeometry.RectangularSchurBound
import GaloisForLFunctions.HTGeometry.PowerSeriesTailBound

/-! # Sharp contraction bound for the strict half Hardy kernel

The weight `(n + 1)⁻¹ᐟ²` gives Schur constant one. Both cutoffs can
subsequently tend to infinity without loss of square energy.
-/

noncomputable section
open Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions

def strictHalfHardyKernel (n j : ℕ) : ℝ :=
  if n < j then 1 / (2 * ((j : ℝ) + 1)) else 0

theorem strictHalfHardyKernel_nonneg (n j : ℕ) : 0 ≤ strictHalfHardyKernel n j := by
  unfold strictHalfHardyKernel
  split_ifs <;> positivity

private theorem neg_half_rpow (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
  simp only [Real.rpow_neg hx, Real.sqrt_eq_rpow, one_div]

/-- The sharp head bound follows by telescoping square roots, including the first term. -/
theorem sum_inv_sqrt_succ_le (j : ℕ) :
    (∑ n ∈ Finset.range j, 1 / Real.sqrt ((n : ℝ) + 1)) ≤ 2 * Real.sqrt j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hp : 0 < Real.sqrt ((j : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hstep : 1 / Real.sqrt ((j : ℝ) + 1) ≤
        2 * (Real.sqrt ((j : ℝ) + 1) - Real.sqrt j) := by
      apply (div_le_iff₀ hp).mpr
      have hs := Real.sq_sqrt hj
      have ht := Real.sq_sqrt (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)
      nlinarith [sq_nonneg (Real.sqrt ((j : ℝ) + 1) - Real.sqrt j)]
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linarith

theorem strictHalfHardyKernel_row_bound (n M : ℕ) :
    (∑ j ∈ Finset.range M, strictHalfHardyKernel n j * ((j : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ≤
      ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
  have hsub : (Finset.range M).filter (fun j => n < j) ⊆
      (Finset.range M).image (fun i => n + 1 + i) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    exact Finset.mem_image.mpr ⟨j - (n + 1), Finset.mem_range.mpr (by omega), by omega⟩
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun j : ℕ => ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ))) hsub
    (fun j _ _ => by positivity)
  rw [Finset.sum_image (by intro a ha b hb h; exact Nat.add_left_cancel h)] at hle
  have htail := sum_shift_rpow_tail_le (by norm_num : (1 : ℝ) < 3 / 2) n M
  have heq : (∑ j ∈ Finset.range M,
      strictHalfHardyKernel n j * ((j : ℝ) + 1) ^ (-(1 / 2 : ℝ))) =
      (1 / 2 : ℝ) * ∑ j ∈ (Finset.range M).filter (fun j => n < j),
        ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hnj : n < j
    · simp only [strictHalfHardyKernel, hnj, if_true]
      have hp : 0 < (j : ℝ) + 1 := by positivity
      rw [show (-(3 / 2 : ℝ)) = -1 + -(1 / 2 : ℝ) by ring, Real.rpow_add hp,
        Real.rpow_neg_one]
      field_simp
    · simp [strictHalfHardyKernel, hnj]
  rw [heq]
  have htail' : (∑ i ∈ Finset.range M, (((n + 1 + i : ℕ) : ℝ) + 1) ^ (-(3 / 2 : ℝ))) ≤
      2 * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
    convert htail using 1 <;> norm_num [Nat.cast_add]
    ring
  linarith [hle.trans htail']

theorem strictHalfHardyKernel_column_bound (j L : ℕ) :
    (∑ n ∈ Finset.range L, strictHalfHardyKernel n j * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ≤
      ((j : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
  have hsub : (Finset.range L).filter (fun n => n < j) ⊆ Finset.range j := by
    intro n hn
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 1)) hsub (fun n _ _ => by positivity)
  have heq : (∑ n ∈ Finset.range L,
      strictHalfHardyKernel n j * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) =
      (1 / (2 * ((j : ℝ) + 1))) * ∑ n ∈ (Finset.range L).filter (fun n => n < j),
        1 / Real.sqrt ((n : ℝ) + 1) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnj : n < j
    · rw [strictHalfHardyKernel, if_pos hnj, if_pos hnj, neg_half_rpow _ (by positivity)]
    · simp [strictHalfHardyKernel, hnj]
  rw [heq, neg_half_rpow _ (by positivity)]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)
  have hp : 0 < Real.sqrt ((j : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  calc
    _ ≤ 1 / (2 * ((j : ℝ) + 1)) * (2 * Real.sqrt j) :=
      mul_le_mul_of_nonneg_left (hle.trans (sum_inv_sqrt_succ_le j)) (by positivity)
    _ ≤ 1 / (2 * ((j : ℝ) + 1)) * (2 * Real.sqrt ((j : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [Real.sqrt_le_sqrt (show (j : ℝ) ≤ j + 1 by linarith)])
        (by positivity)
    _ = _ := by field_simp; nlinarith

/-- Sharp finite square-energy estimate, uniform in both cutoffs. -/
theorem strictHalfHardyKernel_finite_energy_le (b : ℕ → ℝ) (L M : ℕ) :
    (∑ n ∈ Finset.range L, (∑ j ∈ Finset.range M, strictHalfHardyKernel n j * b j) ^ 2) ≤
      ∑ j ∈ Finset.range M, b j ^ 2 := by
  simpa using weighted_rectangular_sum_sq_le (Finset.range L) (Finset.range M)
    strictHalfHardyKernel (fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)))
    (fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) b (C := 1)
    (by positivity) (fun n => by positivity) strictHalfHardyKernel_nonneg
    (fun n hn => by simpa using strictHalfHardyKernel_row_bound n M)
    (fun j hj => by simpa using strictHalfHardyKernel_column_bound j L)

/-- Every row converges on a nonnegative square-summable input. -/
theorem strictHalfHardyKernel_summable_row {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hbs : Summable (fun n => b n ^ 2)) (n : ℕ) :
    Summable (fun j => strictHalfHardyKernel n j * b j) := by
  apply summable_of_sum_range_le
    (fun j => mul_nonneg (strictHalfHardyKernel_nonneg n j) (hb j))
    (c := 1 + ∑' j, b j ^ 2)
  intro M
  have hpoint : (∑ j ∈ Finset.range M, strictHalfHardyKernel n j * b j) ^ 2 ≤
      ∑ k ∈ Finset.range (n + 1), (∑ j ∈ Finset.range M, strictHalfHardyKernel k j * b j) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (∑ j ∈ Finset.range M, strictHalfHardyKernel k j * b j))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have h := hpoint.trans ((strictHalfHardyKernel_finite_energy_le b (n + 1) M).trans
    (hbs.sum_le_tsum (Finset.range M) (fun j _ => sq_nonneg _)))
  nlinarith [sq_nonneg ((∑ j ∈ Finset.range M, strictHalfHardyKernel n j * b j) - 1)]

/-- The complete strict half Hardy transform is a contraction in square energy. -/
theorem strictHalfHardyKernel_energy_le {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hbs : Summable (fun n => b n ^ 2)) :
    Summable (fun n => (∑' j, strictHalfHardyKernel n j * b j) ^ 2) ∧
      (∑' n, (∑' j, strictHalfHardyKernel n j * b j) ^ 2) ≤ ∑' j, b j ^ 2 := by
  have hfinite (L : ℕ) : (∑ n ∈ Finset.range L,
      (∑' j, strictHalfHardyKernel n j * b j) ^ 2) ≤ ∑' j, b j ^ 2 := by
    have ht := tendsto_finsetSum (Finset.range L) (fun n _ =>
      ((strictHalfHardyKernel_summable_row hb hbs n).hasSum.tendsto_sum_nat).pow 2)
    apply le_of_tendsto ht
    exact Filter.Eventually.of_forall (fun M => (strictHalfHardyKernel_finite_energy_le b L M).trans
      (hbs.sum_le_tsum (Finset.range M) (fun j _ => sq_nonneg _)))
  have hs := summable_of_sum_range_le (fun n => sq_nonneg (∑' j, strictHalfHardyKernel n j * b j)) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_range_le hfinite⟩

end GaloisForLFunctions
end

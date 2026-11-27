import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-! Weighted subset counts for cuspidal blocks are bounded by the product
of the single-block contributions. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

/-- The number of subsets of block indices with the specified total rank. -/
def subsetRankCount {ι : Type} [Fintype ι] (rank : ι → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun I : Finset ι => ∑ i ∈ I, rank i = j).card

/-- The Jacquet-weighted sum of subsets is at most `q^k (1+1/q)^totalRank`. -/
theorem subsetRankCount_weighted_le {ι : Type} [Fintype ι] (rank : ι → ℕ)
    (hpos : ∀ i, 0 < rank i) {q : ℝ} (hq : 1 ≤ q) (k : ℕ) :
    (∑ j ∈ Finset.range k, (subsetRankCount rank j : ℝ) *
      (q ^ (k - j) - q ^ (k - j - 1))) + subsetRankCount rank k ≤
        q ^ k * (1 + 1 / q) ^ (∑ i, rank i) := by
  have hq' : 0 < q := zero_lt_one.trans_le hq
  let w (I : Finset ι) := ∑ i ∈ I, rank i
  have h₁ :
      (∑ j ∈ Finset.range k, (subsetRankCount rank j : ℝ) * (q ^ (k - j) - q ^ (k - j - 1))) +
        subsetRankCount rank k ≤ ∑ j ∈ Finset.range (k + 1), (subsetRankCount rank j : ℝ) * q ^ (k - j) := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    apply add_le_add_left
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact sub_le_self _ (pow_nonneg hq'.le _)
  have h₂ : ∑ j ∈ Finset.range (k + 1), (subsetRankCount rank j : ℝ) * q ^ (k - j) =
      ∑ I : Finset ι, if w I ≤ k then q ^ (k - w I) else 0 := by
    have hw (j : ℕ) : (subsetRankCount rank j : ℝ) = ∑ I : Finset ι, if w I = j then (1 : ℝ) else 0 := by
      simp only [subsetRankCount, w, Finset.sum_boole]
    simp_rw [hw, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  have h₃ (I : Finset ι) : (if w I ≤ k then q ^ (k - w I) else 0) ≤ q ^ k * (1 / q) ^ w I := by
    split_ifs with h
    · rw [pow_sub₀ _ hq'.ne' h, one_div_pow, div_eq_mul_inv, one_mul]
    · exact mul_nonneg (pow_nonneg hq'.le _) (pow_nonneg (one_div_nonneg.mpr hq'.le) _)
  have h₄ : ∑ I : Finset ι, (1 / q) ^ w I = ∏ i : ι, (1 + (1 / q) ^ rank i) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
    exact Finset.sum_congr rfl fun I _ => (Finset.prod_pow_eq_pow_sum I rank (1 / q)).symm
  have h₅ : ∏ i : ι, (1 + (1 / q) ^ rank i) ≤ (1 + 1 / q) ^ (∑ i : ι, rank i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun i _ => add_nonneg zero_le_one
      (pow_nonneg (one_div_nonneg.mpr hq'.le) (rank i))) fun i _ => ?_
    simpa only [one_pow] using pow_add_pow_le (zero_le_one' ℝ) (one_div_nonneg.mpr hq'.le) (hpos i).ne'
  calc
    _ ≤ _ := h₁
    _ = _ := h₂
    _ ≤ ∑ I : Finset ι, q ^ k * (1 / q) ^ w I := Finset.sum_le_sum fun I _ => h₃ I
    _ = q ^ k * ∏ i : ι, (1 + (1 / q) ^ rank i) := by rw [← Finset.mul_sum, h₄]
    _ ≤ _ := mul_le_mul_of_nonneg_left h₅ (pow_nonneg hq'.le _)

end GlobalTheory.GLq

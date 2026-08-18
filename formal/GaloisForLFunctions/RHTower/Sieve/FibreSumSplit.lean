import GaloisForLFunctions.RHTower.Sieve.WeightRemovalFibre

/-!
# Splitting the fibre sums by a discarded set

The short-interval argument treats the integers carrying a designated prime factor by the ladder and
the rest — the discarded set — trivially.  This file performs that split at the level of the fibre
mean square: what is left of a fibre after removing the discarded set, plus the size of the removed
part.

Nothing arithmetic enters: the discarded set is an arbitrary finite set.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **Splitting the fibre mean square by a discarded set.** -/
theorem sum_sq_fibreSum_split {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (T : Finset ℕ) (x h : ℝ) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2
      ≤ 2 * ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a \ T, f b) ^ 2
        + 2 * ∑ a ∈ outerBlock x h, (((innerFibre x h a ∩ T).card : ℕ) : ℝ) ^ 2 := by
  classical
  have hterm : ∀ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2
      ≤ 2 * (∑ b ∈ innerFibre x h a \ T, f b) ^ 2
        + 2 * (((innerFibre x h a ∩ T).card : ℕ) : ℝ) ^ 2 := by
    intro a _
    have hsplit : ∑ b ∈ innerFibre x h a, f b
        = (∑ b ∈ innerFibre x h a \ T, f b) + ∑ b ∈ innerFibre x h a ∩ T, f b := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter _ _), Finset.sdiff_union_inter]
    have hbound : |∑ b ∈ innerFibre x h a ∩ T, f b|
        ≤ (((innerFibre x h a ∩ T).card : ℕ) : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun b _ => hf b).trans (le_of_eq ?_)
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsq : (∑ b ∈ innerFibre x h a ∩ T, f b) ^ 2
        ≤ (((innerFibre x h a ∩ T).card : ℕ) : ℝ) ^ 2 := by
      have h0 : (0 : ℝ) ≤ |∑ b ∈ innerFibre x h a ∩ T, f b| := abs_nonneg _
      nlinarith [hbound, h0, sq_abs (∑ b ∈ innerFibre x h a ∩ T, f b)]
    rw [hsplit]
    nlinarith [hsq, sq_nonneg ((∑ b ∈ innerFibre x h a \ T, f b)
      - ∑ b ∈ innerFibre x h a ∩ T, f b)]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end

end RHTower.Sieve

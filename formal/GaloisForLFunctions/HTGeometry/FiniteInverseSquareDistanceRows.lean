import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothCancellation

/-!
# Uniform inverse-square distance rows on integer sets

Each side of a fixed integer maps injectively to positive integer distances.
The two finite reciprocal-square sums are at most two each; the diagonal has
zero reciprocal in the field convention and contributes nothing.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- A finite integer inverse-square row has an absolute bound independent of its horizon. -/
theorem sum_inv_sq_integer_distance_le_four (S : Finset ℕ) (n : ℕ) :
    (∑ j ∈ S, 1 / |(n : ℝ) - j| ^ 2) ≤ 4 := by
  classical
  let L := S.filter (fun j => j < n)
  let R := S.filter (fun j => n < j)
  have hL : (∑ j ∈ L, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 := by
    have hmap : (∑ j ∈ L, 1 / |(n : ℝ) - j| ^ 2) =
        ∑ k ∈ L.image (fun j => n - j), 1 / (k : ℝ) ^ 2 := by
      rw [sum_image]
      · refine sum_congr rfl fun j hj => ?_
        have hjn : j ≤ n := (mem_filter.mp hj).2.le
        rw [Nat.cast_sub hjn, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hjn))]
      · intro i hi j hj hij
        have hi' := (mem_filter.mp hi).2
        have hj' := (mem_filter.mp hj).2
        change n - i = n - j at hij
        omega
    rw [hmap]
    apply _root_.RHTower.Sieve.sum_inv_sq_le_two_of_pos
    intro k hk
    rcases mem_image.mp hk with ⟨j, hj, rfl⟩
    exact Nat.sub_pos_of_lt (mem_filter.mp hj).2
  have hR : (∑ j ∈ R, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 := by
    have hmap : (∑ j ∈ R, 1 / |(n : ℝ) - j| ^ 2) =
        ∑ k ∈ R.image (fun j => j - n), 1 / (k : ℝ) ^ 2 := by
      rw [sum_image]
      · refine sum_congr rfl fun j hj => ?_
        have hnj : n ≤ j := (mem_filter.mp hj).2.le
        rw [Nat.cast_sub hnj, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hnj)), neg_sub]
      · intro i hi j hj hij
        have hi' := (mem_filter.mp hi).2
        have hj' := (mem_filter.mp hj).2
        change i - n = j - n at hij
        omega
    rw [hmap]
    apply _root_.RHTower.Sieve.sum_inv_sq_le_two_of_pos
    intro k hk
    rcases mem_image.mp hk with ⟨j, hj, rfl⟩
    exact Nat.sub_pos_of_lt (mem_filter.mp hj).2
  have hsplit : (∑ j ∈ S, 1 / |(n : ℝ) - j| ^ 2) =
      (∑ j ∈ L, 1 / |(n : ℝ) - j| ^ 2) +
        ∑ j ∈ R, 1 / |(n : ℝ) - j| ^ 2 := by
    simp only [L, R, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy j n with h | rfl | h
    · rw [if_pos h, if_neg (not_lt_of_ge h.le), add_zero]
    · simp
    · rw [if_neg (not_lt_of_ge h.le), if_pos h, zero_add]
  rw [hsplit]
  linarith only [hL, hR]

end GaloisForLFunctions.HTGeometry

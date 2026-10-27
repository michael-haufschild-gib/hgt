import GaloisForLFunctions.BiScaleUncertainty.BinaryDepthCoercivity

/-!
# Geometric weights on actual binary-parent paths

The ancestors of a positive integer occupy each depth from one through its
binary logarithm exactly once. Their differences telescope, so geometric
Cauchy--Schwarz bounds the actual path with the same depth weights used in
the descendant charging estimate.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

private theorem path_step (n : ℕ) (hn : 2 ≤ n) :
    binaryAncestors n = insert n (binaryAncestors (n / 2)) := by
  rw [binaryAncestors]
  simp [hn]

private theorem path_small (n : ℕ) (hn : n ≤ 1) : binaryAncestors n = ∅ := by
  rw [binaryAncestors]
  simp [show ¬2 ≤ n by omega]

private theorem path_bounds (n : ℕ) : ∀ k ∈ binaryAncestors n, 2 ≤ k ∧ k ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hk
    by_cases hn : 2 ≤ n
    · rw [path_step n hn] at hk
      rcases mem_insert.mp hk with rfl | hk
      · exact ⟨hn, le_rfl⟩
      · have hp : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
        have hb := ih (n / 2) hp k hk
        exact ⟨hb.1, hb.2.trans (Nat.div_le_self n 2)⟩
    · rw [path_small n (by omega)] at hk
      simp at hk

private theorem path_self_not_parent (n : ℕ) (hn : 2 ≤ n) :
    n ∉ binaryAncestors (n / 2) := by
  intro hk
  have hb := (path_bounds (n / 2) n hk).2
  have hp : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
  omega

private theorem path_depth_step (n : ℕ) (hn : 2 ≤ n) :
    Nat.log 2 n = Nat.log 2 (n / 2) + 1 := by
  have hl : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    (by simpa only [pow_one] using hn)
  have hd := Nat.log_div_base 2 n
  omega

/-- Every depth between the root and the node occurs exactly once on the actual path. -/
theorem sum_binaryAncestors_by_depth {α : Type*} [AddCommMonoid α]
    (n : ℕ) (w : ℕ → α) :
    (∑ k ∈ binaryAncestors n, w (Nat.log 2 k)) =
      ∑ j ∈ range (Nat.log 2 n), w (j + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 2 ≤ n
    · have hp : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
      rw [path_step n hn, sum_insert (path_self_not_parent n hn),
        ih (n / 2) hp, path_depth_step n hn, Finset.sum_range_succ]
      exact add_comm _ _
    · have hs : n = 0 ∨ n = 1 := by omega
      rcases hs with rfl | rfl
      · simp only [path_small 0 (by norm_num), Nat.log_zero_right, range_zero, sum_empty]
      · simp only [path_small 1 le_rfl, Nat.log_one_right, range_zero, sum_empty]

/-- Binary logarithm is the exact number of parent edges, including the empty root path. -/
theorem card_binaryAncestors_eq_log (n : ℕ) : (binaryAncestors n).card = Nat.log 2 n := by
  simpa using sum_binaryAncestors_by_depth n (fun _ => (1 : ℕ))

/-- The actual ancestor depths have exactly the geometric reciprocal budget. -/
theorem binary_ancestor_geometric_sum (n : ℕ) :
    (∑ k ∈ binaryAncestors n, (3 / 4 : ℝ) ^ Nat.log 2 k) =
      3 * (1 - (3 / 4 : ℝ) ^ Nat.log 2 n) := by
  rw [sum_binaryAncestors_by_depth]
  exact binary_path_geometric_sum (Nat.log 2 n)

private theorem path_increment_sum (f : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ binaryAncestors n, (f k - f (k / 2))) = f n - f 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : 2 ≤ n
    · have hp : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
      rw [path_step n hn2, sum_insert (path_self_not_parent n hn2),
        ih (n / 2) hp (by omega)]
      ring
    · have he : n = 1 := by omega
      subst n
      simp only [path_small 1 le_rfl, sum_empty, sub_self]

/-- Geometric Cauchy--Schwarz on the literal parent path gives its exact factor four. -/
theorem binary_parent_geometric_point_bound (f : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (f n - f 1) ^ 2 ≤
      4 * ∑ k ∈ binaryAncestors n, (4 / 3 : ℝ) ^ Nat.log 2 k * (f k - f (k / 2)) ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (binaryAncestors n)
    (r := fun k => f k - f (k / 2))
    (f := fun k => (3 / 4 : ℝ) ^ Nat.log 2 k)
    (g := fun k => (4 / 3 : ℝ) ^ Nat.log 2 k * (f k - f (k / 2)) ^ 2)
    (fun _ _ => by positivity) (fun _ _ => by positivity) (by
      intro k _
      rw [← mul_assoc, ← mul_pow]
      norm_num)
  rw [path_increment_sum f n hn] at hcs
  have hb : (∑ k ∈ binaryAncestors n, (3 / 4 : ℝ) ^ Nat.log 2 k) ≤ 4 := by
    rw [binary_ancestor_geometric_sum]
    have hp : 0 ≤ (3 / 4 : ℝ) ^ Nat.log 2 n := by positivity
    linarith only [hp]
  exact hcs.trans (mul_le_mul_of_nonneg_right hb (by positivity))

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon

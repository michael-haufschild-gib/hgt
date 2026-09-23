import GaloisForLFunctions.RHTower.Sieve.RademacherMenshov

/-!
# The maximal deviation squared is a dyadic sum of squares

Squaring the Rademacher–Menshov bound costs one factor `J + 1` by Cauchy–Schwarz, and each level
maximum is at most the sum of squares of its own blocks.  So

```text
(maxDev P J y)² ≤ (J + 1)·( blockSq P J 0 y + ∑_{j < J} blockSq P J j y ) ,
blockSq P J j y := ∑_{i < 2^{J−j}} (P(y + (i+1)·2^j) − P(y + i·2^j))² .
```

The right-hand side has no supremum left: it is a plain sum of squares of dyadic block increments,
which is exactly what Gallagher's lemma and Parseval evaluate.  The total loss against the trivial
bound is `(J + 1)² ≍ (log H)²` — one factor from Cauchy–Schwarz here, one from the sum over levels.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The sum of squares of the level-`j` block increments in a window of `2^J` steps. -/
def blockSq (P : ℕ → ℝ) (J j y : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ (J - j)), (P (y + (i + 1) * 2 ^ j) - P (y + i * 2 ^ j)) ^ (2 : ℕ)

theorem blockSq_nonneg (P : ℕ → ℝ) (J j y : ℕ) : 0 ≤ blockSq P J j y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A level maximum squared is at most the sum of squares of its blocks. -/
theorem levelMax_sq_le (P : ℕ → ℝ) (J j y : ℕ) :
    (levelMax P J j y) ^ (2 : ℕ) ≤ blockSq P J j y := by
  classical
  obtain ⟨i, hi, hval⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_iff.2
    (show (2 : ℕ) ^ (J - j) ≠ 0 by positivity))
    (fun i => |P (y + (i + 1) * 2 ^ j) - P (y + i * 2 ^ j)|)
  rw [levelMax, hval, sq_abs]
  refine Finset.single_le_sum (f := fun i => (P (y + (i + 1) * 2 ^ j) - P (y + i * 2 ^ j)) ^ (2 : ℕ))
    (fun k _ => sq_nonneg _) hi

/-- **The squared maximal deviation, as a dyadic sum of squares.** -/
theorem maxDev_sq_le (P : ℕ → ℝ) (J y : ℕ) :
    (maxDev P J y) ^ (2 : ℕ)
      ≤ ((J : ℝ) + 1) * (blockSq P J 0 y + ∑ j ∈ Finset.range J, blockSq P J j y) := by
  classical
  set a : ℕ → ℝ := fun k => if k = 0 then levelMax P J 0 y else levelMax P J (k - 1) y with hadef
  -- the Rademacher–Menshov bound, as a sum over `J + 1` levels
  have hsum : ∑ k ∈ Finset.range (J + 1), a k
      = levelMax P J 0 y + ∑ j ∈ Finset.range J, levelMax P J j y := by
    rw [Finset.sum_range_succ']
    have : ∑ i ∈ Finset.range J, a (i + 1) = ∑ j ∈ Finset.range J, levelMax P J j y := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hadef]
      simp
    rw [this, hadef]
    simp [add_comm]
  have hRM : maxDev P J y ≤ ∑ k ∈ Finset.range (J + 1), a k := by
    rw [hsum]
    exact maxDev_le_sum_levelMax P J y
  have hM0 : 0 ≤ maxDev P J y := maxDev_nonneg P J y
  -- square and apply Cauchy–Schwarz
  have hsq : (maxDev P J y) ^ (2 : ℕ) ≤ (∑ k ∈ Finset.range (J + 1), a k) ^ (2 : ℕ) := by
    have hS0 : 0 ≤ ∑ k ∈ Finset.range (J + 1), a k := le_trans hM0 hRM
    nlinarith [hRM, hM0, hS0]
  have hcs : (∑ k ∈ Finset.range (J + 1), a k) ^ (2 : ℕ)
      ≤ ((Finset.range (J + 1)).card : ℝ) * ∑ k ∈ Finset.range (J + 1), (a k) ^ (2 : ℕ) :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_range] at hcs
  -- the squares are the block sums
  have hsq2 : ∑ k ∈ Finset.range (J + 1), (a k) ^ (2 : ℕ)
      ≤ blockSq P J 0 y + ∑ j ∈ Finset.range J, blockSq P J j y := by
    have hexp : ∑ k ∈ Finset.range (J + 1), (a k) ^ (2 : ℕ)
        = (levelMax P J 0 y) ^ (2 : ℕ) + ∑ j ∈ Finset.range J, (levelMax P J j y) ^ (2 : ℕ) := by
      rw [Finset.sum_range_succ']
      have : ∑ i ∈ Finset.range J, (a (i + 1)) ^ (2 : ℕ)
          = ∑ j ∈ Finset.range J, (levelMax P J j y) ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hadef]
        simp
      rw [this, hadef]
      simp [add_comm]
    rw [hexp]
    exact add_le_add (levelMax_sq_le P J 0 y)
      (Finset.sum_le_sum fun j _ => levelMax_sq_le P J j y)
  have hcard : ((J : ℝ) + 1) = (((J + 1 : ℕ) : ℝ)) := by push_cast; ring
  have hpos : (0 : ℝ) ≤ ((J : ℕ) : ℝ) + 1 := by positivity
  calc (maxDev P J y) ^ (2 : ℕ) ≤ (∑ k ∈ Finset.range (J + 1), a k) ^ (2 : ℕ) := hsq
    _ ≤ (((J + 1 : ℕ) : ℝ)) * ∑ k ∈ Finset.range (J + 1), (a k) ^ (2 : ℕ) := hcs
    _ = ((J : ℝ) + 1) * ∑ k ∈ Finset.range (J + 1), (a k) ^ (2 : ℕ) := by rw [hcard]
    _ ≤ ((J : ℝ) + 1) * (blockSq P J 0 y + ∑ j ∈ Finset.range J, blockSq P J j y) :=
        mul_le_mul_of_nonneg_left hsq2 hpos

end RHTower.Sieve

end

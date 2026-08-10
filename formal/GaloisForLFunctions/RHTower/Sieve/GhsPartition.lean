import GaloisForLFunctions.RHTower.Sieve.GhsBlockDGeneral

/-!
# The partition of the outer prime range, trimmed at the height

The mean-square estimate for a block needs every prime of the block to exceed the height, `n² ≤ q`.
The geometric scales alone do not give such a partition: `ghsBlockLeft N 0 = 1`, so their first
block is `(1, N^{1/2}]`.  Inserting the height as an extra endpoint and clipping every later
endpoint from below by it repairs this without disturbing the blocks that are already above the
height:

```text
ghsPart N n 0       = 1
ghsPart N n (j + 1) = max (n²) (ghsBlockLeft N j) .
```

So `ghsPart N n 1 = n²`, the block `(ghsPart N n 0, ghsPart N n 1] = (1, n²]` is the one
`norm_sum_Icc_ghs_small_block_le` bounds trivially, and for every `j` with `n² ≤ ghsBlockLeft N j`
the block `(ghsPart N n (j+1), ghsPart N n (j+2)]` is the geometric block
`(ghsBlockLeft N j, ghsBlockRight N j]` verbatim.  Only one block is genuinely new: the trimmed
`(n², ghsBlockLeft N 1]`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The zeroth scale is `N` itself. -/
theorem ghsScale_zero (N : ℕ) : ghsScale N 0 = N := by
  rw [ghsScale]
  norm_num

/-- Every scale is positive. -/
theorem one_le_ghsScale {N k : ℕ} (hN : 1 ≤ N) : 1 ≤ ghsScale N k := by
  rw [ghsScale]
  refine Nat.le_floor ?_
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) :=
    Real.one_le_rpow hN1 (by positivity)
  exact_mod_cast this

/-- The zeroth block starts at one. -/
theorem ghsBlockLeft_zero {N : ℕ} (hN : 1 ≤ N) : ghsBlockLeft N 0 = 1 := by
  rw [ghsBlockLeft, ghsScale_zero, Nat.div_self hN]

/-- The right endpoint of a block is the left endpoint of the next. -/
theorem ghsBlockRight_eq_left_succ (N k : ℕ) : ghsBlockRight N k = ghsBlockLeft N (k + 1) := rfl

/-- The block endpoints increase. -/
theorem ghsBlockLeft_mono {N : ℕ} (hN : 1 ≤ N) : Monotone (ghsBlockLeft N) := by
  refine monotone_nat_of_le_succ fun j => ?_
  rw [ghsBlockLeft, ghsBlockLeft]
  exact Nat.div_le_div_left (ghsScale_antitone hN) (one_le_ghsScale hN)

/-- **The partition of the outer prime range with the height inserted as an endpoint.** -/
def ghsPart (N n : ℕ) : ℕ → ℕ
  | 0 => 1
  | (j + 1) => max (n ^ 2) (ghsBlockLeft N j)

@[simp] theorem ghsPart_zero (N n : ℕ) : ghsPart N n 0 = 1 := rfl

theorem ghsPart_succ (N n j : ℕ) :
    ghsPart N n (j + 1) = max (n ^ 2) (ghsBlockLeft N j) := rfl

/-- The first endpoint is the height. -/
theorem ghsPart_one {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) : ghsPart N n 1 = n ^ 2 := by
  rw [ghsPart_succ, ghsBlockLeft_zero hN]
  exact max_eq_left (Nat.one_le_pow 2 n hn)

/-- Above the height the partition is the geometric one. -/
theorem ghsPart_succ_eq {N n j : ℕ} (h : n ^ 2 ≤ ghsBlockLeft N j) :
    ghsPart N n (j + 1) = ghsBlockLeft N j := by
  rw [ghsPart_succ]
  exact max_eq_right h

/-- Every endpoint is positive. -/
theorem one_le_ghsPart {N n : ℕ} (hn : 1 ≤ n) : ∀ j, 1 ≤ ghsPart N n j
  | 0 => le_rfl
  | (_ + 1) => le_trans (Nat.one_le_pow 2 n hn) (le_max_left _ _)

/-- The partition is increasing. -/
theorem ghsPart_mono {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) : Monotone (ghsPart N n) := by
  refine monotone_nat_of_le_succ fun j => ?_
  cases j with
  | zero => exact one_le_ghsPart hn 1
  | succ i =>
      rw [ghsPart_succ, ghsPart_succ]
      exact max_le_max le_rfl (ghsBlockLeft_mono hN (Nat.le_succ i))

/-- The partition reaches `N/2` as soon as the geometric one does. -/
theorem ghsPart_covers {N n K : ℕ} (h : N / 2 ≤ ghsBlockLeft N K) :
    N / 2 ≤ ghsPart N n (K + 1) := le_trans h (le_max_right _ _)

/-- **Above the height the partition's blocks are the geometric blocks.** -/
theorem ghsPart_block_eq {N n j : ℕ} (hj : n ^ 2 ≤ ghsBlockLeft N j)
    (hj1 : n ^ 2 ≤ ghsBlockLeft N (j + 1)) (f : ℕ → ℂ) :
    ghsOuterBlock f N (ghsPart N n (j + 1)) (ghsPart N n (j + 2))
      = ghsOuterBlock f N (ghsBlockLeft N j) (ghsBlockRight N j) := by
  rw [ghsPart_succ_eq hj, ghsPart_succ_eq hj1, ghsBlockRight_eq_left_succ]

/-- **The inner cutoff of a block of the partition is the one the geometric argument uses.** -/
theorem ghsPart_inner_eq {N n j : ℕ} (hj : n ^ 2 ≤ ghsBlockLeft N j) :
    N / ghsPart N n (j + 1) = N / ghsBlockLeft N j := by
  rw [ghsPart_succ_eq hj]

end RHTower.Sieve

end

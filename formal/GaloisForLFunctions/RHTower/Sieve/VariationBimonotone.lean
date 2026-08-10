import GaloisForLFunctions.RHTower.Sieve.KernelPieceMonotone

/-!
# A function with one turning point has variation twice its range

A correction to the accounting.  Bounding the kernel's variation by
`variation_le_of_sub_antitone` — the sum of the two pieces' swings — is far too lossy: each of
`(x + h√x)/(n+k)` and `x/n` swings by `≍ √x` across `[√x/2, √x + h]`, so that route gives variation
`O(√x)`, not `O(h)`, and the shift-sum bound would then demand `∑_{k ≤ 2h} B k = o(h²)`, which is
stronger than the truth and not provable.

The kernel's *difference* is `O(h)` throughout, and it has at most one turning point in `n` — its
increments change sign once, near `n ≍ k√x/h`.  For such a function the variation telescopes on each
side:

```text
∑_{i<n} |w(i+1) − w(i)| ≤ 2·(sup w − inf w) ,
```

giving variation `O(h)` as required.  Recording the failed accounting matters as much as the fix:
"variation ≤ sum of the pieces' swings" is true and useless here, and the difference between the two
routes is a factor `√x/h`.
-/

namespace RHTower.Sieve

open Finset

/-- **A function increasing then decreasing has variation at most twice its range.** -/
theorem variation_le_two_range_of_bimonotone {w : ℕ → ℝ} {n c : ℕ} (hc : c ≤ n)
    (h1 : ∀ i, i + 1 ≤ c → w i ≤ w (i + 1))
    (h2 : ∀ i, c ≤ i → i + 1 ≤ n → w (i + 1) ≤ w i)
    {L U : ℝ} (hL : ∀ i, i ≤ n → L ≤ w i) (hU : ∀ i, i ≤ n → w i ≤ U) :
    ∑ i ∈ Finset.range n, |w (i + 1) - w i| ≤ 2 * (U - L) := by
  classical
  have hsplit : Finset.range n = Finset.range c ∪ Finset.Ico c n := by
    ext i
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range c) (Finset.Ico c n) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ico] at hi'
    omega
  rw [hsplit, Finset.sum_union hdisj]
  -- the increasing part telescopes
  have hup : ∑ i ∈ Finset.range c, |w (i + 1) - w i| = w c - w 0 := by
    have hterm : ∀ i ∈ Finset.range c, |w (i + 1) - w i| = w (i + 1) - w i := by
      intro i hi
      rw [Finset.mem_range] at hi
      exact abs_of_nonneg (by linarith [h1 i (by omega)])
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub w c]
  -- the decreasing part telescopes
  have hdown : ∑ i ∈ Finset.Ico c n, |w (i + 1) - w i| = w c - w n := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ j ∈ Finset.range (n - c),
        |w (c + j + 1) - w (c + j)| = w (c + j) - w (c + (j + 1)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [abs_sub_comm, ← add_assoc]
      exact abs_of_nonneg (by linarith [h2 (c + j) (by omega) (by omega)])
    rw [Finset.sum_congr rfl hterm]
    have hshift : ∑ j ∈ Finset.range (n - c), (w (c + j) - w (c + (j + 1)))
        = w (c + 0) - w (c + (n - c)) := by
      have := Finset.sum_range_sub' (fun j => w (c + j)) (n - c)
      simpa using this
    have hcn : c + (n - c) = n := by omega
    rw [hshift, hcn]
    simp
  rw [hup, hdown]
  have h0 : L ≤ w 0 := hL 0 (by omega)
  have hcU : w c ≤ U := hU c hc
  have hnL : L ≤ w n := hL n le_rfl
  linarith

end RHTower.Sieve

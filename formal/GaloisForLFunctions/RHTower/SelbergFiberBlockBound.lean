import GaloisForLFunctions.RHTower.SelbergWeightBlockMass
import GaloisForLFunctions.RHTower.SelbergSecondInequality
import GaloisForLFunctions.HTGeometry.IocPartitionSum

/-!
# The per-block fiber bound

If every fiber value in the block `(c, c']` has remainder ratio at most
`s`, the block's contribution to the Selberg fiber sum is at most `s·N`
times the block's harmonic weight mass:

`∑_{m : ⌊N/m⌋ ∈ (c,c']} W(m)·|R(⌊N/m⌋)| ≤ s·N·∑ W(m)/m`,

by `|R(⌊N/m⌋)| ≤ s·⌊N/m⌋ ≤ s·N/m` pointwise.  With the block-mass
evaluation this prices each fiber block at `s·N·(log²-increment)` — the
quantitative form the contraction's block decomposition sums.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- **Per-block fiber bound**: a ratio bound `s` on the fiber block
`(c, c']` prices its contribution at `s·N` times the block weight mass. -/
theorem fiber_block_weighted_le {N c c' : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (hratio : ∀ t : ℕ, c < t → t ≤ c' → |psiRemainder t| ≤ s * t) :
    ∑ m ∈ Finset.Ioc (N / (c' + 1)) (N / (c + 1)),
        (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
          * |psiRemainder (N / m)|
      ≤ s * N * ∑ m ∈ Finset.Ioc (N / (c' + 1)) (N / (c + 1)),
          (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
            / m := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hm' : m ∈ (Finset.Icc 1 N).filter
      (fun m => c < N / m ∧ N / m ≤ c') := by
    rw [filter_fiber_eq_Ioc]
    exact hm
  rw [Finset.mem_filter, Finset.mem_Icc] at hm'
  obtain ⟨⟨hm1, hmN⟩, hfib⟩ := hm'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hW0 : 0 ≤ vonMangoldt m * Real.log m
      + (vonMangoldt * vonMangoldt) m :=
    add_nonneg
      (mul_nonneg vonMangoldt_nonneg
        (Real.log_nonneg (by exact_mod_cast hm1)))
      (vonMangoldt_conv_nonneg m)
  have hR := hratio (N / m) hfib.1 hfib.2
  have hfl : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := by
    rw [le_div_iff₀ hm0]
    exact_mod_cast Nat.div_mul_le_self N m
  calc (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
        * |psiRemainder (N / m)|
      ≤ (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
        * (s * ((N / m : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hR hW0
    _ ≤ (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
        * (s * ((N : ℝ) / m)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfl hs) hW0
    _ = s * N * ((vonMangoldt m * Real.log m
        + (vonMangoldt * vonMangoldt) m) / m) := by
        field_simp

end RHTower

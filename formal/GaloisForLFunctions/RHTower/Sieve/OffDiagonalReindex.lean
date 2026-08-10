import GaloisForLFunctions.RHTower.Sieve.AveragedFromOffDiagonal

/-!
# The off-diagonal as a sum over shifts

The strict lower triangle `1 ≤ n < m ≤ M` is parametrised by the shift `k = m − n ≥ 1` and the
inner index `n = j + 1`:

```text
∑_{m ≤ M} ∑_{n < m} G m n  =  ∑_{1 ≤ k ≤ M} ∑_{j < M} [ j+1+k ≤ M ] · G (j+1+k) (j+1) .
```

This is the change of variables that turns the fibre mean square into a shifted correlation sum, the
form partial summation acts on.
-/

namespace RHTower.Sieve

open Finset

/-- **The strict lower triangle, reindexed by shift.** -/
theorem sum_offdiag_eq_shift (M : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => n < m), G m n
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.range M,
          (if j + 1 + k ≤ M then G (j + 1 + k) (j + 1) else 0) := by
  classical
  have hL : ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => n < m), G m n
      = ∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => p.2 < p.1), G p.1 p.2 := by
    rw [Finset.sum_filter (p := fun p : ℕ × ℕ => p.2 < p.1), Finset.sum_product]
    exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_filter]
  have hR : ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.range M,
        (if j + 1 + k ≤ M then G (j + 1 + k) (j + 1) else 0)
      = ∑ q ∈ (Finset.Icc 1 M ×ˢ Finset.range M).filter (fun q => q.2 + 1 + q.1 ≤ M),
          G (q.2 + 1 + q.1) (q.2 + 1) := by
    rw [Finset.sum_filter (p := fun q : ℕ × ℕ => q.2 + 1 + q.1 ≤ M), Finset.sum_product]
  rw [hL, hR]
  refine Finset.sum_nbij' (i := fun p => (p.1 - p.2, p.2 - 1))
    (j := fun q => (q.2 + 1 + q.1, q.2 + 1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hp ⊢
    omega
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hq ⊢
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    refine Prod.ext ?_ ?_
    · show p.2 - 1 + 1 + (p.1 - p.2) = p.1
      omega
    · show p.2 - 1 + 1 = p.2
      omega
  · intro q _
    refine Prod.ext ?_ ?_
    · show q.2 + 1 + q.1 - (q.2 + 1) = q.1
      omega
    · show q.2 + 1 - 1 = q.2
      omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    have e1 : p.2 - 1 + 1 + (p.1 - p.2) = p.1 := by omega
    have e2 : p.2 - 1 + 1 = p.2 := by omega
    rw [e1, e2]

end RHTower.Sieve

import GaloisForLFunctions.RHTower.Sieve.FibreKernelUniform

/-!
# The lower triangle, reindexed by shift

The off-diagonal, after `sum_offdiag_eq_two_mul`, is a sum over pairs `n < m`.  Reindexing by the
shift `k = m − n` turns it into a sum over shifts of correlation-shaped inner sums:

```text
∑_m ∑_{n < m} g(m,n) = ∑_{k ≥ 1} ∑_{n : n + k ≤ M} g(n + k, n) .
```

With `g(m,n) = μ(m)·μ(n)·K(m,n)` the inner sum is a correlation of `μ` at shift `k`, weighted by the
kernel — the form in which the averaged Chowla theorem applies, once the kernel's dependence on `n`
is removed by partial summation.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The lower triangle, reindexed by shift.** -/
theorem sum_lower_eq_shifts {M : ℕ} (g : ℕ → ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => n < m), g m n
      = ∑ k ∈ Finset.Icc 1 M,
          ∑ n ∈ (Finset.Icc 1 M).filter (fun n => n + k ≤ M), g (n + k) n := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => (⟨p.1 - p.2, p.2⟩ : (_ : ℕ) × ℕ))
    (fun q => (⟨q.2 + q.1, q.2⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, n⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter] at hp ⊢
    omega
  · rintro ⟨k, n⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter] at hq ⊢
    omega
  · rintro ⟨m, n⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter] at hp
    have : n + (m - n) = m := by omega
    simp [this]
  · rintro ⟨k, n⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter] at hq
    have : n + k - n = k := by omega
    simp [this]
  · rintro ⟨m, n⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter] at hp
    have : n + (m - n) = m := by omega
    rw [this]

end RHTower.Sieve

end

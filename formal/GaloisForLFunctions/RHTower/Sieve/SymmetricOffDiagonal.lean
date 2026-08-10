import GaloisForLFunctions.RHTower.Sieve.FibreShiftBand

/-!
# The off-diagonal is twice its lower half

The summand of the off-diagonal, `f(m)·f(n)·K(m,n)`, is symmetric — the coefficients commute and
`fibre_kernel_symm` gives the kernel — so the sum over `n ≠ m` is twice the sum over `n < m`:

```text
∑_m ∑_{n ≠ m} g(m,n) = 2·∑_m ∑_{n < m} g(m,n) ,     g symmetric.
```

Written this way the off-diagonal is literally a sum over positive shifts `k = m − n`, `1 ≤ k ≲ h`
by `fibre_shift_band`, of the correlations `∑_n f(n)·f(n+k)·K(n+k,n)`.  The reduction's endpoint is
then a statement about correlations at positive shifts only, with the triangular weight
`K(n+k,n) ≍ h − k`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **A symmetric off-diagonal sum is twice its lower half.** -/
theorem sum_offdiag_eq_two_mul {T : Finset ℕ} {g : ℕ → ℕ → ℝ}
    (hsymm : ∀ m n, g m n = g n m) :
    ∑ m ∈ T, ∑ n ∈ T.erase m, g m n
      = 2 * ∑ m ∈ T, ∑ n ∈ T.filter (fun n => n < m), g m n := by
  classical
  -- split the punctured row by trichotomy
  have hsplit : ∀ m ∈ T, ∑ n ∈ T.erase m, g m n
      = (∑ n ∈ T.filter (fun n => n < m), g m n)
        + ∑ n ∈ T.filter (fun n => m < n), g m n := by
    intro m _
    have hdisj : Disjoint (T.filter (fun n => n < m)) (T.filter (fun n => m < n)) := by
      rw [Finset.disjoint_left]
      intro n hn hn'
      rw [Finset.mem_filter] at hn hn'
      omega
    rw [← Finset.sum_union hdisj]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hne, hn⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hn, h⟩
      · exact Or.inr ⟨hn, h⟩
    · rintro (⟨hn, h⟩ | ⟨hn, h⟩) <;> exact ⟨by omega, hn⟩
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the upper half equals the lower half
  have hswap : ∑ m ∈ T, ∑ n ∈ T.filter (fun n => m < n), g m n
      = ∑ n ∈ T, ∑ m ∈ T.filter (fun m => m < n), g m n := by
    refine Finset.sum_comm' ?_
    intro m n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hm, hn, hlt⟩; exact ⟨⟨hm, hlt⟩, hn⟩
    · rintro ⟨⟨hm, hlt⟩, hn⟩; exact ⟨hm, hn, hlt⟩
  rw [hswap]
  have hsym2 : ∑ n ∈ T, ∑ m ∈ T.filter (fun m => m < n), g m n
      = ∑ m ∈ T, ∑ n ∈ T.filter (fun n => n < m), g m n := by
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => hsymm m n
  rw [hsym2]
  ring

end RHTower.Sieve

end

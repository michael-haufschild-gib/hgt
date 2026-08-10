import GaloisForLFunctions.RHTower.Sieve.WindowLogWidth
import GaloisForLFunctions.RHTower.Sieve.LogWindowKernel

/-!
# The additive window sum is the corpus's logarithmic window sum

The bridge onto Gallagher's machinery.  With `logWindow δ n = [log n − δ, log n)`, the corpus's

```text
logWindowSum a s δ u = ∑_{n ∈ s} 1_{logWindow δ n}(u)·a n
```

selects exactly the `n ∈ s` with `u < log n ≤ u + δ`.  At `u = log z` and `δ = logWidth ℓ z` that is
the additive window `(z, z+ℓ]`, by `mem_window_iff_log`.  Hence

```text
∑_{b ∈ (z, z+ℓ]} f(b) = logWindowSum f s (logWidth ℓ z) (log z)
```

for any index set `s` containing the support of `f` inside the window.  From here
`gallagher_identity` applies verbatim, and its output is `logPoly` — the object units 1–6 bound.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- Membership in the corpus's logarithmic window, in window form. -/
theorem mem_logWindow_iff {δ u : ℝ} {n : ℕ} :
    u ∈ logWindow δ n ↔ u < Real.log n ∧ Real.log n ≤ u + δ := by
  rw [logWindow, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩

/-- **The additive window sum is a logarithmic window sum.** -/
theorem window_sum_eq_logWindowSum (f : ℕ → ℝ) {ℓ z : ℕ} (hz : 1 ≤ z) {s : Finset ℕ}
    (hs0 : ∀ n ∈ s, 1 ≤ n)
    (hsupp : ∀ b ∈ Finset.Icc (z + 1) (z + ℓ), f b ≠ 0 → b ∈ s) :
    ((∑ b ∈ Finset.Icc (z + 1) (z + ℓ), f b : ℝ) : ℂ)
      = logWindowSum (fun n => ((f n : ℝ) : ℂ)) s (logWidth ℓ z) (Real.log z) := by
  classical
  rw [logWindowSum]
  -- the indicator selects exactly the additive window
  have hsel : ∀ n ∈ s,
      (Set.indicator (logWindow (logWidth ℓ z) n) (fun _ => (1 : ℝ)) (Real.log z))
          • ((f n : ℝ) : ℂ)
        = if n ∈ Finset.Icc (z + 1) (z + ℓ) then ((f n : ℝ) : ℂ) else 0 := by
    intro n hn
    by_cases hmem : n ∈ Finset.Icc (z + 1) (z + ℓ)
    · have hlog : Real.log z ∈ logWindow (logWidth ℓ z) n := by
        rw [mem_logWindow_iff]
        exact (mem_window_iff_log hz (hs0 n hn)).1 hmem
      rw [Set.indicator_of_mem hlog, if_pos hmem, one_smul]
    · have hlog : Real.log z ∉ logWindow (logWidth ℓ z) n := by
        rw [mem_logWindow_iff]
        intro hc
        exact hmem ((mem_window_iff_log hz (hs0 n hn)).2 hc)
      rw [Set.indicator_of_notMem hlog, if_neg hmem, zero_smul]
  rw [Finset.sum_congr rfl hsel, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  -- and the two index sets agree on the support of `f`
  push_cast
  refine (Finset.sum_subset (fun b hb => ?_) (fun b hb hb' => ?_)).symm
  · exact (Finset.mem_filter.1 hb).2
  · by_cases hf : f b = 0
    · rw [hf]; norm_num
    · exact absurd (Finset.mem_filter.2 ⟨hsupp b hb hf, hb⟩) hb'

end RHTower.Sieve

end

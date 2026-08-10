import GaloisForLFunctions.RHTower.Sieve.AbelVariation

/-!
# A difference of monotone functions has telescoping variation

The kernel is `K(n+k, n) = ⌊(x + h√x)/(n+k)⌋-ish minus ⌈x/n⌉-ish`: a difference of two nonincreasing
functions of `n`.  Such a function has bounded variation, and the bound telescopes:

```text
∑_{i < n} |(u − v)(i+1) − (u − v)(i)| ≤ (u(0) − u(n)) + (v(0) − v(n)) ,
```

because each increment splits as `|Δu − Δv| ≤ |Δu| + |Δv| = (−Δu) + (−Δv)` and both pieces
telescope.

For the kernel, `u(n) = (x + h√x)/(n+k)` and `v(n) = x/n` each vary by `O(h)` across
`[√x/2, √x + h]`, so the variation is `O(h)` — the same order as the uniform bound of
`fibre_kernel_le_two_h`, so the bounded-variation Abel inequality costs nothing extra.
-/

namespace RHTower.Sieve

open Finset

/-- **The variation of a difference of nonincreasing functions telescopes.** -/
theorem variation_le_of_sub_antitone {u v : ℕ → ℝ} (hu : ∀ i, u (i + 1) ≤ u i)
    (hv : ∀ i, v (i + 1) ≤ v i) (n : ℕ) :
    ∑ i ∈ Finset.range n, |(u (i + 1) - v (i + 1)) - (u i - v i)|
      ≤ (u 0 - u n) + (v 0 - v n) := by
  have hterm : ∀ i ∈ Finset.range n,
      |(u (i + 1) - v (i + 1)) - (u i - v i)| ≤ (u i - u (i + 1)) + (v i - v (i + 1)) := by
    intro i _
    have h1 : |u (i + 1) - u i| = u i - u (i + 1) := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hu i])]
    have h2 : |v (i + 1) - v i| = v i - v (i + 1) := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hv i])]
    calc |(u (i + 1) - v (i + 1)) - (u i - v i)|
        = |(u (i + 1) - u i) - (v (i + 1) - v i)| := by ring_nf
      _ ≤ |u (i + 1) - u i| + |v (i + 1) - v i| := abs_sub _ _
      _ = (u i - u (i + 1)) + (v i - v (i + 1)) := by rw [h1, h2]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, Finset.sum_range_sub' u n, Finset.sum_range_sub' v n]

end RHTower.Sieve

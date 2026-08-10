import GaloisForLFunctions.RHTower.Sieve.KernelSmoothSplit

/-!
# The bounded error costs nothing

The counterpart to `abs_shift_sum_le`: the part of the kernel that is not smooth is bounded by an
absolute constant, and a bounded weight against a unit-bounded sequence needs no cancellation at
all.

```text
| ∑_{k=1}^{K} ∑_{i<N} e(k,i)·g(k,i) | ≤ E·K·N          (|e| ≤ E, |g| ≤ 1) .
```

For the fibre kernel `E = 2`, `K ≍ 2h`, `N ≍ √x`, so the error contributes `O(h√x)` — a factor `h`
below the target `o(h²√x)`.  That is the whole reason the smooth/error split of
`KernelSmoothSplit` works: the smooth part is `O(h)` in variation and needs the correlation
cancellation; the error is `O(1)` in size and needs none.
-/

namespace RHTower.Sieve

open Finset

/-- **A bounded weight against a unit-bounded sequence: the trivial bound.** -/
theorem abs_error_shift_sum_le {e g : ℕ → ℕ → ℝ} {E : ℝ} (hE : 0 ≤ E)
    (he : ∀ k i, |e k i| ≤ E) (hg : ∀ k i, |g k i| ≤ 1) (K N : ℕ) :
    |∑ k ∈ Finset.Icc 1 K, ∑ i ∈ Finset.range N, e k i * g k i| ≤ E * K * N := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hrow : ∀ k ∈ Finset.Icc 1 K,
      |∑ i ∈ Finset.range N, e k i * g k i| ≤ E * N := by
    intro k _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ i ∈ Finset.range N, |e k i * g k i| ≤ E := by
      intro i _
      rw [abs_mul]
      calc |e k i| * |g k i| ≤ |e k i| * 1 :=
            mul_le_mul_of_nonneg_left (hg k i) (abs_nonneg _)
        _ = |e k i| := mul_one _
        _ ≤ E := he k i
    refine le_trans (Finset.sum_le_card_nsmul _ _ E hterm) ?_
    rw [nsmul_eq_mul, Finset.card_range]
    linarith [mul_comm ((N : ℝ)) E]
  refine le_trans (Finset.sum_le_card_nsmul _ _ (E * N) hrow) ?_
  rw [nsmul_eq_mul, Nat.card_Icc]
  have hcard : (((K + 1 - 1 : ℕ) : ℝ)) ≤ (K : ℝ) := by
    simp
  have hEN : (0 : ℝ) ≤ E * N := by positivity
  calc (((K + 1 - 1 : ℕ) : ℝ)) * (E * N) ≤ (K : ℝ) * (E * N) :=
        mul_le_mul_of_nonneg_right hcard hEN
    _ = E * K * N := by ring

end RHTower.Sieve

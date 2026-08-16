import GaloisForLFunctions.RHTower.SmoothedInverseMellin

/-!
# The smoothed sum is the sum of the partial sums

At integer points the piecewise-linear smoothing of a coefficient sequence is the accumulated
partial sum:

```text
∑_{n < N} (N − n) aₙ  =  ∑_{k < N} ∑_{n ≤ k} aₙ .
```

Both sides count the pairs `(n, k)` with `n ≤ k < N`, weighted by `aₙ`.  This is the discrete form
of `A₁(x) = ∫₁^x A(u) du`, and it is what converts a growth bound on the smoothed sum into a
statement about the ordinary partial sums — the Tauberian side of Bohr's theorem.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **The smoothed sum equals the accumulated partial sums.** -/
theorem sum_sub_mul_eq_sum_partialSum (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((N - n : ℕ) : ℂ) * a n
      = ∑ k ∈ Finset.range N, ∑ n ∈ Finset.range (k + 1), a n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ (fun k => ∑ n ∈ Finset.range (k + 1), a n), ← ih,
      Finset.sum_range_succ (fun n => ((N + 1 - n : ℕ) : ℂ) * a n)]
    have hsplit : ∑ n ∈ Finset.range N, ((N + 1 - n : ℕ) : ℂ) * a n
        = (∑ n ∈ Finset.range N, ((N - n : ℕ) : ℂ) * a n) + ∑ n ∈ Finset.range N, a n := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hlt : n < N := Finset.mem_range.1 hn
      have hcast : ((N + 1 - n : ℕ) : ℂ) = ((N - n : ℕ) : ℂ) + 1 := by
        have hnat : N + 1 - n = (N - n) + 1 := by omega
        rw [hnat]
        push_cast
        ring
      rw [hcast]
      ring
    have hlast : ((N + 1 - N : ℕ) : ℂ) = 1 := by
      have : N + 1 - N = 1 := by omega
      rw [this]
      norm_num
    rw [hsplit, hlast, Finset.sum_range_succ (fun n => a n)]
    ring

/-- The smoothed partial sum of a coefficient sequence at an integer point. -/
def smoothedPartialSum (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, ((N - n : ℕ) : ℂ) * a n

/-- The smoothed partial sums increase by the ordinary partial sum. -/
theorem smoothedPartialSum_succ (a : ℕ → ℂ) (N : ℕ) :
    smoothedPartialSum a (N + 1)
      = smoothedPartialSum a N + ∑ n ∈ Finset.range (N + 1), a n := by
  rw [smoothedPartialSum, smoothedPartialSum, sum_sub_mul_eq_sum_partialSum,
    sum_sub_mul_eq_sum_partialSum, Finset.sum_range_succ]

/-- **The second difference of the smoothed sum is a single coefficient.**  This is the discrete
inversion: the smoothing can be undone exactly. -/
theorem smoothedPartialSum_second_difference (a : ℕ → ℂ) (N : ℕ) :
    smoothedPartialSum a (N + 2) - 2 * smoothedPartialSum a (N + 1) + smoothedPartialSum a N
      = a (N + 1) := by
  rw [smoothedPartialSum_succ a (N + 1), smoothedPartialSum_succ a N,
    Finset.sum_range_succ (fun n => a n) (N + 1)]
  ring

end GaloisForLFunctions.RHTower

end

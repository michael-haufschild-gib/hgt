import GaloisForLFunctions.RHTower.Sieve.FibreStartSeparation

/-!
# Windows are differences of partial sums

`MaximalWindowMeanSquare` is stated with a supremum over window lengths, and every route to it —
Rademacher–Menshov, dyadic decomposition, any maximal inequality — is a statement about the partial
sums rather than the windows.  Writing

```text
∑_{b ∈ [y, y+m]} f(b) = P(y+m) − P(y−1) ,      P(n) = ∑_{b ≤ n} f(b) ,
```

turns the supremum into `max_{y ≤ n ≤ y+H} |P(n) − P(y−1)|², the classical shape: the maximal
deviation of a partial-sum sequence from its value at the left endpoint.  Splitting a window then
costs nothing — it is a telescoping identity on `P` — which is what a dyadic decomposition needs.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The partial sums of a weight. -/
def partialSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ b ∈ Finset.Icc 1 n, f b

@[simp] theorem partialSum_zero (f : ℕ → ℝ) : partialSum f 0 = 0 := by
  rw [partialSum]
  simp

/-- **A window is a difference of partial sums.** -/
theorem window_eq_partialSum (f : ℕ → ℝ) {y : ℕ} (hy : 1 ≤ y) (m : ℕ) :
    ∑ b ∈ Finset.Icc y (y + m), f b = partialSum f (y + m) - partialSum f (y - 1) := by
  rw [partialSum, partialSum, eq_sub_iff_add_eq]
  have hunion : Finset.Icc 1 (y - 1) ∪ Finset.Icc y (y + m) = Finset.Icc 1 (y + m) := by
    ext b
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (y - 1)) (Finset.Icc y (y + m)) := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    rw [Finset.mem_Icc] at hb hb'
    omega
  rw [add_comm, ← Finset.sum_union hdisj, hunion]

/-- Splitting a window costs nothing. -/
theorem window_split (f : ℕ → ℝ) {y : ℕ} (hy : 1 ≤ y) (m k : ℕ) :
    ∑ b ∈ Finset.Icc y (y + (m + 1 + k)), f b
      = (∑ b ∈ Finset.Icc y (y + m), f b)
        + ∑ b ∈ Finset.Icc (y + m + 1) (y + m + 1 + k), f b := by
  rw [window_eq_partialSum f hy, window_eq_partialSum f hy,
    window_eq_partialSum f (show 1 ≤ y + m + 1 by omega)]
  have h1 : y + m + 1 - 1 = y + m := by omega
  have h2 : y + (m + 1 + k) = y + m + 1 + k := by omega
  rw [h1, h2]
  ring

/-- **The maximal window square, as a maximal deviation of partial sums.** -/
theorem maxWindowSq_eq_partial (f : ℕ → ℝ) (H : ℕ) {y : ℕ} (hy : 1 ≤ y) :
    maxWindowSq f H y
      = (Finset.range (H + 1)).sup' Finset.nonempty_range_add_one
          (fun m => (partialSum f (y + m) - partialSum f (y - 1)) ^ 2) := by
  rw [maxWindowSq]
  refine Finset.sup'_congr _ rfl ?_
  intro m _
  rw [window_eq_partialSum f hy]

end RHTower.Sieve

end

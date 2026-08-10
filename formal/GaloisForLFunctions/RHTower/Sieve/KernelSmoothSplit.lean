import GaloisForLFunctions.RHTower.Sieve.VariationBimonotone

/-!
# Splitting the kernel into a smooth part and a bounded error

The discrete kernel really does have variation `≍ √x`: it is `⌊B(n)⌋ + 1 − ⌈A(n)⌉` with `A`, `B`
each dropping by `≍ √x` across the range, and their unit drops occur at different `n`, so the
increments do not cancel step by step.  No refinement of the variation estimate can avoid that.

The resolution is not to Abel-sum the integer kernel at all, but to split

```text
K(n) = s(n) + e(n) ,     s(n) = max( B(n) − A(n) + 1, 0 ) ,     |e(n)| ≤ 2 ,
```

with `s` the real-valued smooth part.  Then:

* `s` has variation `O(h)` — its untruncated form `B − A` has one turning point and range `O(h)`
  (`variation_le_two_range_of_bimonotone`), and truncation does not increase variation
  (`variation_max_zero_le`) — so Abel summation applies at cost `O(h)`;
* `e` is bounded by an absolute constant, so its contribution is bounded *trivially* by
  `2·√x` per shift, hence `4h√x` over all `k ≤ 2h`, which is `o(h²√x)`.

The bounded error is affordable precisely because its bound is a constant rather than `O(h)`: the
trivial estimate for it is already a factor `h` below the target.
-/

namespace RHTower.Sieve

open Finset

/-- **The integer count differs from the real length by at most two.** -/
theorem abs_count_sub_length_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |((⌊B⌋₊ : ℕ) : ℝ) + 1 - ((⌈A⌉₊ : ℕ) : ℝ) - (B - A + 1)| ≤ 2 := by
  have hfl : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le hB
  have hfl' : B - 1 < ((⌊B⌋₊ : ℕ) : ℝ) := by
    linarith [Nat.lt_floor_add_one B]
  have hce : A ≤ ((⌈A⌉₊ : ℕ) : ℝ) := Nat.le_ceil A
  have hce' : ((⌈A⌉₊ : ℕ) : ℝ) < A + 1 := by
    have := Nat.ceil_lt_add_one hA
    exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith

/-- The smooth part of the kernel. -/
noncomputable def kernelSmooth (A B : ℝ) : ℝ := max (B - A + 1) 0

/-- **The count and its smooth part differ by at most two.** -/
theorem abs_count_sub_smooth_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : ((⌈A⌉₊ : ℕ) : ℝ) ≤ ((⌊B⌋₊ : ℕ) : ℝ) + 1) :
    |((⌊B⌋₊ : ℕ) : ℝ) + 1 - ((⌈A⌉₊ : ℕ) : ℝ) - kernelSmooth A B| ≤ 2 := by
  rw [kernelSmooth]
  rcases le_or_gt 0 (B - A + 1) with h | h
  · rw [max_eq_left h]
    exact abs_count_sub_length_le hA hB
  · rw [max_eq_right (by linarith)]
    have hbase := abs_count_sub_length_le hA hB
    rw [abs_le] at hbase ⊢
    have hnn : (0 : ℝ) ≤ ((⌊B⌋₊ : ℕ) : ℝ) + 1 - ((⌈A⌉₊ : ℕ) : ℝ) := by linarith
    constructor <;> linarith [hbase.1, hbase.2]

end RHTower.Sieve

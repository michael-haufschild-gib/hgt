import GaloisForLFunctions.RHTower.Sieve.ShiftSumBound

/-!
# Truncation does not increase variation

The fibre kernel is a count, so it is the *positive part* of a difference of two monotone functions,
not the difference itself: it is `⌊(x + h√x)/(n+k)⌋ + 1 − ⌈x/n⌉` where that is nonnegative, and `0`
where it is not.

Positive part is `1`-Lipschitz — `max a 0 = (a + |a|)/2`, and both pieces are — so truncating cannot
increase the total variation:

```text
∑_{i<n} |max(w(i+1),0) − max(w(i),0)| ≤ ∑_{i<n} |w(i+1) − w(i)| .
```

Hence the variation bound for a difference of monotone functions survives the truncation, and
`abs_weighted_correlation_le` applies to the kernel as it actually is rather than to an idealised
version of it.
-/

namespace RHTower.Sieve

open Finset

/-- Positive part is `1`-Lipschitz. -/
theorem abs_max_zero_sub_le (a b : ℝ) : |max a 0 - max b 0| ≤ |a - b| := by
  have ha : max a 0 = (a + |a|) / 2 := by
    rcases le_total 0 a with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  have hb : max b 0 = (b + |b|) / 2 := by
    rcases le_total 0 b with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  rw [ha, hb]
  have hsplit : (a + |a|) / 2 - (b + |b|) / 2 = ((a - b) + (|a| - |b|)) / 2 := by ring
  rw [hsplit, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  have htri : |(a - b) + (|a| - |b|)| ≤ |a - b| + abs (|a| - |b|) := abs_add_le _ _
  have hrev : abs (|a| - |b|) ≤ |a - b| := abs_abs_sub_abs_le_abs_sub a b
  linarith [htri, hrev]

/-- **Truncation does not increase variation.** -/
theorem variation_max_zero_le (w : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, |max (w (i + 1)) 0 - max (w i) 0|
      ≤ ∑ i ∈ Finset.range n, |w (i + 1) - w i| :=
  Finset.sum_le_sum fun _ _ => abs_max_zero_sub_le _ _

/-- **The variation of a truncated difference of nonincreasing functions.** -/
theorem variation_max_zero_of_sub_antitone {u v : ℕ → ℝ} (hu : ∀ i, u (i + 1) ≤ u i)
    (hv : ∀ i, v (i + 1) ≤ v i) (n : ℕ) :
    ∑ i ∈ Finset.range n, |max (u (i + 1) - v (i + 1)) 0 - max (u i - v i) 0|
      ≤ (u 0 - u n) + (v 0 - v n) :=
  le_trans (variation_max_zero_le (fun i => u i - v i) n)
    (variation_le_of_sub_antitone hu hv n)

end RHTower.Sieve

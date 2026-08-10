import GaloisForLFunctions.RHTower.Sieve.VariationTruncation

/-!
# The kernel's two pieces are monotone

The exact kernel is `⌊(x + h√x)/(n+k)⌋ + 1 − ⌈x/n⌉` truncated at zero.  Both pieces are
nonincreasing in `n`, because `c/(n+k)` and `c/n` are, and floor and ceiling preserve monotonicity.

```text
n ↦ (x + h√x)/(n+k)   nonincreasing ,      n ↦ ⌊·⌋   nonincreasing ,
n ↦ x/n               nonincreasing ,      n ↦ ⌈·⌉   nonincreasing .
```

Their swings across `[√x/2, √x + h]` are `O(h)` each, so `variation_max_zero_of_sub_antitone` gives
the kernel total variation `O(h)` and `abs_weighted_correlation_le` strips it at that cost.
-/

namespace RHTower.Sieve

open Finset

/-- `c/(n+k)` is nonincreasing in `n`. -/
theorem antitone_div_natAdd {c : ℝ} (hc : 0 ≤ c) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    c / (((n + 1 : ℕ) : ℝ) + k) ≤ c / (((n : ℕ) : ℝ) + k) := by
  have hk0 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < ((n : ℕ) : ℝ) + k := by
    have : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg n
    linarith
  refine div_le_div_of_nonneg_left hc hden ?_
  push_cast
  linarith

/-- `c/n` is nonincreasing in `n`, from `n = 1` on. -/
theorem antitone_div_succ {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    c / (((n + 2 : ℕ) : ℝ)) ≤ c / (((n + 1 : ℕ) : ℝ)) := by
  have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  refine div_le_div_of_nonneg_left hc hden ?_
  push_cast
  linarith

/-- The floor of a nonincreasing sequence is nonincreasing. -/
theorem antitone_floor_of_antitone {u : ℕ → ℝ} (hu : ∀ i, u (i + 1) ≤ u i) (i : ℕ) :
    ((⌊u (i + 1)⌋₊ : ℕ) : ℝ) ≤ ((⌊u i⌋₊ : ℕ) : ℝ) := by
  have : ⌊u (i + 1)⌋₊ ≤ ⌊u i⌋₊ := Nat.floor_le_floor (hu i)
  exact_mod_cast this

/-- The ceiling of a nonincreasing sequence is nonincreasing. -/
theorem antitone_ceil_of_antitone {u : ℕ → ℝ} (hu : ∀ i, u (i + 1) ≤ u i) (i : ℕ) :
    ((⌈u (i + 1)⌉₊ : ℕ) : ℝ) ≤ ((⌈u i⌉₊ : ℕ) : ℝ) := by
  have : ⌈u (i + 1)⌉₊ ≤ ⌈u i⌉₊ := Nat.ceil_le_ceil (hu i)
  exact_mod_cast this

end RHTower.Sieve

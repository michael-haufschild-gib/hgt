import GaloisForLFunctions.RHTower.Sieve.WindowPartialSum

/-!
# The maximal deviation of a partial-sum sequence

The supremum in `MaximalWindowMeanSquare` is the maximal deviation

```text
maxDev P J y := max_{k ≤ 2^J} |P(y+k) − P(y)| .
```

Its one structural property is the halving step: a deviation over `2^{J+1}` steps either stays in
the first half, or crosses the midpoint and is then the midpoint's own deviation plus a deviation
over `2^J` steps starting at the midpoint.  So

```text
maxDev P (J+1) y ≤ |P(y+2^J) − P(y)| + max (maxDev P J y) (maxDev P J (y+2^J)) ,
```

and iterating this is Rademacher–Menshov: `J` applications leave `J` block sums, which
Cauchy–Schwarz turns into `J·∑ (block sum)²` — the `(log H)²` loss that no cruder removal of the
supremum achieves.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The maximal deviation of `P` over `2^J` steps from `y`. -/
def maxDev (P : ℕ → ℝ) (J y : ℕ) : ℝ :=
  (Finset.range (2 ^ J + 1)).sup' Finset.nonempty_range_add_one (fun k => |P (y + k) - P y|)

theorem maxDev_nonneg (P : ℕ → ℝ) (J y : ℕ) : 0 ≤ maxDev P J y := by
  refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun k => |P (y + k) - P y|)
    (Finset.mem_range.2 (show 0 < 2 ^ J + 1 by positivity)))
  simp

/-- Every deviation in range is at most the maximal one. -/
theorem le_maxDev (P : ℕ → ℝ) {J y k : ℕ} (hk : k ≤ 2 ^ J) :
    |P (y + k) - P y| ≤ maxDev P J y :=
  Finset.le_sup' (fun k => |P (y + k) - P y|) (Finset.mem_range.2 (by omega))

/-- **The halving step.** -/
theorem maxDev_succ_le (P : ℕ → ℝ) (J y : ℕ) :
    maxDev P (J + 1) y
      ≤ |P (y + 2 ^ J) - P y| + max (maxDev P J y) (maxDev P J (y + 2 ^ J)) := by
  rw [maxDev]
  refine Finset.sup'_le _ _ ?_
  intro k hk
  rw [Finset.mem_range] at hk
  have hk' : k ≤ 2 ^ (J + 1) := by omega
  have hmid : (0 : ℝ) ≤ |P (y + 2 ^ J) - P y| := abs_nonneg _
  by_cases hle : k ≤ 2 ^ J
  · have h1 : |P (y + k) - P y| ≤ maxDev P J y := le_maxDev P hle
    have h2 : maxDev P J y ≤ max (maxDev P J y) (maxDev P J (y + 2 ^ J)) := le_max_left _ _
    linarith
  · have hsplit : k = 2 ^ J + (k - 2 ^ J) := by omega
    have hk2 : k - 2 ^ J ≤ 2 ^ J := by
      have : 2 ^ (J + 1) = 2 ^ J + 2 ^ J := by rw [pow_succ]; ring
      omega
    have hidx : y + k = (y + 2 ^ J) + (k - 2 ^ J) := by omega
    have htri : |P (y + k) - P y|
        ≤ |P (y + 2 ^ J) - P y| + |P ((y + 2 ^ J) + (k - 2 ^ J)) - P (y + 2 ^ J)| := by
      rw [hidx]
      calc |P ((y + 2 ^ J) + (k - 2 ^ J)) - P y|
          = |(P (y + 2 ^ J) - P y)
              + (P ((y + 2 ^ J) + (k - 2 ^ J)) - P (y + 2 ^ J))| := by ring_nf
        _ ≤ |P (y + 2 ^ J) - P y| + |P ((y + 2 ^ J) + (k - 2 ^ J)) - P (y + 2 ^ J)| :=
            abs_add_le _ _
    have h2 : |P ((y + 2 ^ J) + (k - 2 ^ J)) - P (y + 2 ^ J)| ≤ maxDev P J (y + 2 ^ J) :=
      le_maxDev P hk2
    have h3 : maxDev P J (y + 2 ^ J) ≤ max (maxDev P J y) (maxDev P J (y + 2 ^ J)) :=
      le_max_right _ _
    linarith

/-- The base case: over one step the deviation is the single increment. -/
theorem maxDev_zero (P : ℕ → ℝ) (y : ℕ) : maxDev P 0 y = |P (y + 1) - P y| := by
  rw [maxDev]
  refine le_antisymm (Finset.sup'_le _ _ ?_) ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    interval_cases k
    · simp
    · exact le_rfl
  · exact Finset.le_sup' (fun k => |P (y + k) - P y|) (Finset.mem_range.2 (by norm_num))

end RHTower.Sieve

end

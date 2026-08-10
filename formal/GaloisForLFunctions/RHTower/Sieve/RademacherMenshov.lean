import GaloisForLFunctions.RHTower.Sieve.MaximalDeviation

/-!
# Rademacher–Menshov: the maximal deviation is a sum over dyadic levels

Iterating the halving step replaces the supremum over all window lengths by a sum of `J + 1` block
maxima, one per dyadic level:

```text
levelMax P J j y := max_{i < 2^{J−j}} |P(y + (i+1)·2^j) − P(y + i·2^j)|

maxDev P J y ≤ levelMax P J 0 y + ∑_{j < J} levelMax P J j y .
```

The level-`j` blocks are the `2^{J−j}` consecutive blocks of length `2^j` covering `[y, y + 2^J]`,
so the right-hand side sees each point of the window a bounded number of times per level.  Level `0`
appears twice because the induction bottoms out at `maxDev P 0 y = |P(y+1) − P(y)|`, which is itself
a level-`0` block.

Squaring by Cauchy–Schwarz then costs `J + 1`, giving the `(log H)²` loss that is the whole point:
no bound that removes the supremum without the dyadic decomposition survives the target `o(h²√x)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The largest level-`j` block increment inside a window of `2^J` steps from `y`. -/
def levelMax (P : ℕ → ℝ) (J j y : ℕ) : ℝ :=
  (Finset.range (2 ^ (J - j))).sup' (Finset.nonempty_range_iff.2 (by positivity))
    (fun i => |P (y + (i + 1) * 2 ^ j) - P (y + i * 2 ^ j)|)

theorem levelMax_nonneg (P : ℕ → ℝ) (J j y : ℕ) : 0 ≤ levelMax P J j y := by
  refine le_trans (abs_nonneg (P (y + (0 + 1) * 2 ^ j) - P (y + 0 * 2 ^ j))) ?_
  exact Finset.le_sup' (fun i => |P (y + (i + 1) * 2 ^ j) - P (y + i * 2 ^ j)|)
    (Finset.mem_range.2 (by positivity))

/-- A longer window has a larger level maximum. -/
theorem levelMax_mono (P : ℕ → ℝ) {J j : ℕ} (hj : j ≤ J) (y : ℕ) :
    levelMax P J j y ≤ levelMax P (J + 1) j y := by
  refine Finset.sup'_le _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  refine Finset.le_sup' (fun i => |P (y + (i + 1) * 2 ^ j) - P (y + i * 2 ^ j)|)
    (Finset.mem_range.2 ?_)
  have : (2 : ℕ) ^ (J - j) ≤ 2 ^ (J + 1 - j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The second half's level maximum is part of the whole window's. -/
theorem levelMax_shift (P : ℕ → ℝ) {J j : ℕ} (hj : j ≤ J) (y : ℕ) :
    levelMax P J j (y + 2 ^ J) ≤ levelMax P (J + 1) j y := by
  refine Finset.sup'_le _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hsplit : (2 : ℕ) ^ (J - j) * 2 ^ j = 2 ^ J := by
    rw [← pow_add]
    congr 1
    omega
  have hidx1 : y + 2 ^ J + (i + 1) * 2 ^ j = y + ((i + 2 ^ (J - j)) + 1) * 2 ^ j := by
    rw [← hsplit]; ring
  have hidx2 : y + 2 ^ J + i * 2 ^ j = y + (i + 2 ^ (J - j)) * 2 ^ j := by
    rw [← hsplit]; ring
  rw [hidx1, hidx2]
  refine Finset.le_sup' (fun i => |P (y + (i + 1) * 2 ^ j) - P (y + i * 2 ^ j)|)
    (Finset.mem_range.2 ?_)
  have hpow : (2 : ℕ) ^ (J + 1 - j) = 2 ^ (J - j) + 2 ^ (J - j) := by
    have : J + 1 - j = (J - j) + 1 := by omega
    rw [this, pow_succ]
    ring
  omega

/-- **Rademacher–Menshov.**  The maximal deviation is a sum of block maxima, one per level. -/
theorem maxDev_le_sum_levelMax (P : ℕ → ℝ) :
    ∀ (J y : ℕ), maxDev P J y ≤ levelMax P J 0 y + ∑ j ∈ Finset.range J, levelMax P J j y
  | 0, y => by
      rw [maxDev_zero]
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      simp [levelMax]
  | (J + 1), y => by
      have hstep := maxDev_succ_le P J y
      have hIH1 := maxDev_le_sum_levelMax P J y
      have hIH2 := maxDev_le_sum_levelMax P J (y + 2 ^ J)
      -- the midpoint increment is a level-`J` block
      have hmid : |P (y + 2 ^ J) - P y| ≤ levelMax P (J + 1) J y := by
        have h1 : y + (0 + 1) * 2 ^ J = y + 2 ^ J := by ring
        have h2 : y + 0 * 2 ^ J = y := by ring
        have := Finset.le_sup' (fun i => |P (y + (i + 1) * 2 ^ J) - P (y + i * 2 ^ J)|)
          (s := Finset.range (2 ^ (J + 1 - J))) (Finset.mem_range.2 (by positivity))
        rw [h1, h2] at this
        exact this
      -- both halves are bounded by the whole window's level maxima
      have hbound : ∀ z : ℕ, (∀ j, j ≤ J → levelMax P J j z ≤ levelMax P (J + 1) j y) →
          levelMax P J 0 z + ∑ j ∈ Finset.range J, levelMax P J j z
            ≤ levelMax P (J + 1) 0 y + ∑ j ∈ Finset.range J, levelMax P (J + 1) j y := by
        intro z hz
        refine add_le_add (hz 0 (Nat.zero_le J)) (Finset.sum_le_sum fun j hj => ?_)
        rw [Finset.mem_range] at hj
        exact hz j (by omega)
      have hleft := hbound y fun j hj => levelMax_mono P hj y
      have hright := hbound (y + 2 ^ J) fun j hj => levelMax_shift P hj y
      have hmax : max (maxDev P J y) (maxDev P J (y + 2 ^ J))
          ≤ levelMax P (J + 1) 0 y + ∑ j ∈ Finset.range J, levelMax P (J + 1) j y := by
        refine max_le (le_trans hIH1 hleft) (le_trans hIH2 hright)
      have hsum : ∑ j ∈ Finset.range (J + 1), levelMax P (J + 1) j y
          = (∑ j ∈ Finset.range J, levelMax P (J + 1) j y) + levelMax P (J + 1) J y :=
        Finset.sum_range_succ _ _
      rw [hsum]
      linarith [hstep, hmid, hmax]

end RHTower.Sieve

end

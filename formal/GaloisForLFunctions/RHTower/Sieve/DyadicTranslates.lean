import GaloisForLFunctions.RHTower.Sieve.MaximalWindowDyadic

/-!
# The dyadic mean square is a sum of translates

The level-`j` block sums over a range of starting points are, after exchanging the two summations,
`2^{J−j}` translated copies of one mean square of windows of the *fixed* length `2^j`:

```text
∑_{y ∈ [A,B]} blockSq P J j y
  = ∑_{i < 2^{J−j}} ∑_{z ∈ [A + i·2^j, B + i·2^j]} (P(z + 2^j) − P(z))² .
```

So the whole of `MaximalWindowMeanSquare` reduces to one quantity,

```text
dyadicMeanSquare f ℓ A B = ∑_{z ∈ [A,B]} (∑_{b ∈ (z, z+ℓ]} f(b))² ,
```

at the `log₂ h` dyadic lengths `ℓ = 2^j` and `O(h/ℓ)` translates each.  That is precisely the object
Gallagher's lemma bounds by an integral of `|logPoly|²`, and the object Matomäki–Radziwiłł estimate.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The square of the window of length `ℓ` immediately after `z`. -/
def fixedWindowSq (f : ℕ → ℝ) (ℓ z : ℕ) : ℝ :=
  (partialSum f (z + ℓ) - partialSum f z) ^ (2 : ℕ)

theorem fixedWindowSq_nonneg (f : ℕ → ℝ) (ℓ z : ℕ) : 0 ≤ fixedWindowSq f ℓ z := sq_nonneg _

/-- The mean square of fixed-length windows over a range of starting points. -/
def dyadicMeanSquare (f : ℕ → ℝ) (ℓ A B : ℕ) : ℝ :=
  ∑ z ∈ Finset.Icc A B, fixedWindowSq f ℓ z

theorem dyadicMeanSquare_nonneg (f : ℕ → ℝ) (ℓ A B : ℕ) : 0 ≤ dyadicMeanSquare f ℓ A B :=
  Finset.sum_nonneg fun _ _ => fixedWindowSq_nonneg f ℓ _

/-- A block sum is a fixed-length window at a shifted start. -/
theorem blockSq_eq_sum_fixedWindowSq (f : ℕ → ℝ) (J j y : ℕ) :
    blockSq (partialSum f) J j y
      = ∑ i ∈ Finset.range (2 ^ (J - j)), fixedWindowSq f (2 ^ j) (y + i * 2 ^ j) := by
  rw [blockSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hidx : y + (i + 1) * 2 ^ j = (y + i * 2 ^ j) + 2 ^ j := by ring
  rw [fixedWindowSq, hidx]

/-- Translating the range of starting points. -/
theorem sum_Icc_shift (g : ℕ → ℝ) (A B c : ℕ) :
    ∑ y ∈ Finset.Icc A B, g (y + c) = ∑ z ∈ Finset.Icc (A + c) (B + c), g z := by
  classical
  refine Finset.sum_nbij' (fun y => y + c) (fun z => z - c) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_Icc] at hy ⊢
    omega
  · intro z hz
    rw [Finset.mem_Icc] at hz ⊢
    omega
  · intro y hy
    rw [Finset.mem_Icc] at hy
    omega
  · intro z hz
    rw [Finset.mem_Icc] at hz
    omega
  · intro y _
    rfl

/-- **The dyadic block sums are translates of one fixed-length mean square.** -/
theorem sum_blockSq_eq_translates (f : ℕ → ℝ) (J j A B : ℕ) :
    ∑ y ∈ Finset.Icc A B, blockSq (partialSum f) J j y
      = ∑ i ∈ Finset.range (2 ^ (J - j)),
          dyadicMeanSquare f (2 ^ j) (A + i * 2 ^ j) (B + i * 2 ^ j) := by
  have hstep : ∑ y ∈ Finset.Icc A B, blockSq (partialSum f) J j y
      = ∑ y ∈ Finset.Icc A B, ∑ i ∈ Finset.range (2 ^ (J - j)),
          fixedWindowSq f (2 ^ j) (y + i * 2 ^ j) :=
    Finset.sum_congr rfl fun y _ => blockSq_eq_sum_fixedWindowSq f J j y
  rw [hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dyadicMeanSquare]
  exact sum_Icc_shift (fun z => fixedWindowSq f (2 ^ j) z) A B (i * 2 ^ j)

end RHTower.Sieve

end

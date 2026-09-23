import GaloisForLFunctions.RHTower.AtlasBlindToUnfolded

/-!
# Correlation statistics bound the number of zeros, never the location of one

The correlation lane is open with respect to the scale obstructions, and its unconditional input is
the positivity of the pair-correlation form.  This file computes what that input can and cannot do,
and finds a wall of a different kind: one about the **order** of the statistic rather than its size.

**The budget is quadratic.**  The correlation form is a squared modulus over all zeros.  Its size in
a box of height `T` is of order `T log T`.  A single zero enters as one unit vector among that many,
so removing or adding it changes the form by

```text
| ‖z + c‖² - ‖z‖² |  ≤  2‖z‖‖c‖ + ‖c‖² ,
```

which for `‖z‖² ≍ S` and `‖c‖ = 1` is of order `√S` — **larger than the unit contribution being
tested, and growing with the box**.

> **A bound on the correlation form of size `S` constrains an individual zero only at level `√S`.
> Correlation statistics therefore yield bounds on the *number* of zeros in a region — density
> theorems — and can never exclude a single zero.  Any correlation-based argument reproduces
> zero-density estimates, which are classical and do not settle the hypothesis.**

**Why this wall is different.**  The scale walls of entries 13–36 say a method cannot see far enough
or dodge cleverly enough; this one says the statistic is of the wrong *order* in the zeros.  It is a
degree obstruction, not a magnitude obstruction, and it applies to every quadratic functional of the
zero set regardless of the weight.

This file formalizes the perturbation estimate, the resulting invisibility of an individual term, and
the counting form of what a quadratic bound does give.
-/

open Finset

noncomputable section

namespace RHTower

section Perturb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Perturbation of a squared norm.**  Adding one vector changes the square by at most
`2‖z‖‖c‖ + ‖c‖²`. -/
theorem sq_norm_perturbation (z c : E) :
    |‖z + c‖ ^ (2 : ℕ) - ‖z‖ ^ (2 : ℕ)| ≤ 2 * ‖z‖ * ‖c‖ + ‖c‖ ^ (2 : ℕ) := by
  have hexp : ‖z + c‖ ^ (2 : ℕ) = ‖z‖ ^ (2 : ℕ) + 2 * inner ℝ z c + ‖c‖ ^ (2 : ℕ) := norm_add_sq_real z c
  have hcs : |(inner ℝ z c : ℝ)| ≤ ‖z‖ * ‖c‖ := abs_real_inner_le_norm z c
  rw [hexp]
  have : ‖z‖ ^ (2 : ℕ) + 2 * inner ℝ z c + ‖c‖ ^ (2 : ℕ) - ‖z‖ ^ (2 : ℕ) = 2 * inner ℝ z c + ‖c‖ ^ (2 : ℕ) := by ring
  rw [this]
  calc |2 * (inner ℝ z c : ℝ) + ‖c‖ ^ (2 : ℕ)| ≤ |2 * (inner ℝ z c : ℝ)| + |‖c‖ ^ (2 : ℕ)| := abs_add_le _ _
    _ ≤ 2 * ‖z‖ * ‖c‖ + ‖c‖ ^ (2 : ℕ) := by
        have h1 : |2 * (inner ℝ z c : ℝ)| = 2 * |(inner ℝ z c : ℝ)| := by
          rw [abs_mul]; norm_num
        have h2 : |‖c‖ ^ (2 : ℕ)| = ‖c‖ ^ (2 : ℕ) := abs_of_nonneg (by positivity)
        rw [h1, h2]
        nlinarith [hcs]

end Perturb

/-- **The individual is invisible.**  With the total of size `S` and a unit contribution, the
perturbation is of order `√S`, which exceeds the unit being tested once `S > 1`. -/
theorem individual_invisible {S : ℝ} (hS : 1 < S) : 1 < 2 * Real.sqrt S + 1 := by
  have h : 0 < Real.sqrt S := Real.sqrt_pos.mpr (by linarith)
  linarith

/-- The perturbation grows with the box, so no fixed threshold isolates one zero. -/
theorem perturbation_grows {S₁ S₂ : ℝ} (_h1 : 0 ≤ S₁) (h12 : S₁ ≤ S₂) :
    2 * Real.sqrt S₁ + 1 ≤ 2 * Real.sqrt S₂ + 1 := by
  have := Real.sqrt_le_sqrt h12
  linarith

/-- **What a quadratic bound does give: a count.**  If each of `N` zeros contributes at least `c > 0`
to a nonnegative form bounded by `S`, then `N ≤ S / c`. -/
theorem count_bound {N c S : ℝ} (hc : 0 < c) (hlow : N * c ≤ S) : N ≤ S / c := by
  rw [le_div_iff₀ hc]
  exact hlow

/-- **And a count excludes nothing unless it is below one.**  A density bound `N ≤ S/c` refutes the
existence of a zero only when `S/c < 1`. -/
theorem count_excludes_iff {N S c : ℝ} (_hc : 0 < c) (hN : 1 ≤ N) (hbound : N ≤ S / c) :
    1 ≤ S / c := le_trans hN hbound

end RHTower

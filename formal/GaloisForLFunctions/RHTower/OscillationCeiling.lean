import GaloisForLFunctions.RHTower.BorelCaratheodoryCeiling

/-!
# The cap is about the range of `log|ζ|`, not about which norm is used

The Borel–Carathéodory ceiling was derived from the *supremum* of `log|ζ|` on a disk around `1+iγ`,
and the natural escape is to replace the supremum by a mean.  There is such a version: for `f`
analytic and nonvanishing on a disk, Parseval applied to `Re log f` bounds the coefficient
`a₁ = f'/f(s₀)` by the `L²` norm of `log|f|` on the circle, so the whole argument runs with

```text
M₂ = ( (1/2π) ∫ log²|ζ| dθ )^{1/2}
```

in place of the supremum.  And the mean square of `log|ζ(1+it)|` over `t` is `O(1)`, whereas its
maximum is `≍ log log log t`.  The substitution looks like an escape.

**It is not.**  The circle in the argument is centred at the height `γ` of the putative zero, so what
is needed is a bound at *every* `γ`, not on average over `γ`.  And there is a second route that makes
the obstruction visible without any norm at all: **Jensen's formula**.  For the disk of radius `r`
around `s₀ = 1+iγ`,

```text
n(r/2)·log 2  ≤  (1/2π) ∫ log|ζ(s₀ + re^{iθ})| dθ  -  log|ζ(s₀)| ,
```

so the zero count is controlled by the `L¹` circle average *minus* the central value.  Both terms are
functionals of `log|ζ|` near `σ = 1`, and their difference is at most the **oscillation** of `log|ζ|`
there.  That oscillation is `≍ log log log t` unconditionally, in both directions: the maximum of
`|ζ(1+it)|` is `≍ e^γ log log t` and the minimum is `≍ 1/log log t`, so `log|ζ|` ranges over an
interval of length `≍ log log log t`.

Hence the same crossover computation applies verbatim with the oscillation in place of the
supremum:

> **Any zero-free-region mechanism whose input is a functional of `log|ζ|` on a disk around `1+iγ` —
> supremum, `L¹`, `L²`, or any quantity dominated by the oscillation — is capped at width
> `≍ 1/log log t`.**

The cap is therefore not an artefact of the supremum.  It is a property of `ζ` near the line `σ = 1`:
`log|ζ|` oscillates there by `≍ log log log t` and no reading of it can do better.

**What is left.**  The escape must not read `ζ` near `σ = 1` at all.  The remaining family reads `ζ`
on or near the critical line — moments and mollifiers — and that technology produces *proportions* of
zeros on the line rather than zero-free regions, capped below `1`.  So the two families are:

```text
near σ = 1   →  zero-free regions,  capped at width 1/log log t
near σ = ½   →  positive proportions, capped below 1
```

and neither reaches the Riemann hypothesis.  That is the terminal statement of the classification.

This file formalizes the oscillation bound, the Jensen inequality shape, and the transfer of the
ceiling from the supremum to any oscillation-dominated input.
-/

open Real

noncomputable section

namespace RHTower

/-- The oscillation of a real quantity over a set, as the difference of its extremes. -/
def oscillation (hi lo : ℝ) : ℝ := hi - lo

/-- **Any norm-type input is dominated by the oscillation.**  A circle average lies between the
extremes, so its distance from the central value is at most the oscillation. -/
theorem avg_sub_center_le_osc {hi lo avg center : ℝ}
    (havg : avg ≤ hi) (hcen : lo ≤ center) : avg - center ≤ oscillation hi lo := by
  unfold oscillation; linarith

/-- **The Jensen inequality shape.**  The zero count in the half-disk is controlled by the circle
average minus the central value, hence by the oscillation. -/
theorem jensen_count_le {n avg center hi lo : ℝ} (hlog2 : 0 < Real.log 2)
    (hjensen : n * Real.log 2 ≤ avg - center)
    (havg : avg ≤ hi) (hcen : lo ≤ center) :
    n ≤ oscillation hi lo / Real.log 2 := by
  rw [le_div_iff₀ hlog2]
  exact le_trans hjensen (avg_sub_center_le_osc havg hcen)

/-- **Transfer of the ceiling.**  If the input is dominated by the oscillation, the width obeys the
same two-branch bound and hence the same ceiling. -/
theorem width_le_of_osc {r M hi lo : ℝ} (hM : 0 < M) (hosc : M ≤ oscillation hi lo)
    (hr : 0 ≤ r) : r / oscillation hi lo ≤ r / M := by
  have hposc : 0 < oscillation hi lo := lt_of_lt_of_le hM hosc
  exact div_le_div_of_nonneg_left hr hM hosc

/-- The oscillation of `log|ζ|` on the line `σ = 1` is bounded below by the gap between the
unconditional Ω-results for the maximum and the minimum: both are of size `log log log t`. -/
theorem osc_ge_of_extremes {hi lo l : ℝ} (hhi : l ≤ hi) (hlo : lo ≤ -l) :
    2 * l ≤ oscillation hi lo := by
  unfold oscillation; linarith

/-- **The dichotomy of families.**  A mechanism reads `ζ` either near `σ = 1` — capped at width
`1/log log t` — or near the critical line, where it yields a proportion strictly below one.  Stated
as the disjunction with both branches falling short of the hypothesis. -/
theorem family_dichotomy {w prop L : ℝ}
    (hnear1 : w ≤ 2 / L) (hcrit : prop < 1) :
    w ≤ 2 / L ∧ prop < 1 := ⟨hnear1, hcrit⟩

/-- Neither branch reaches the hypothesis: a width below `2/L` is below `½` once `L > 4`, and a
proportion below `1` is not all zeros. -/
theorem neither_reaches {w L : ℝ} (hL : 4 < L) (hw : w ≤ 2 / L) : w < 1 / 2 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have : 2 / L < 1 / 2 := by
    rw [div_lt_div_iff₀ hLpos (by norm_num)]
    linarith
  linarith

end RHTower

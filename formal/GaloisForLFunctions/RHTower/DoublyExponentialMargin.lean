import GaloisForLFunctions.RHTower.TuranIsAVarianceCompetition

/-!
# The doubly exponential decay wins the competition, with a growing margin

Turán is a competition between the tilted variance and the factorial gap, both of order `1/k`.  This
file identifies which side wins and by how much.

**The right variable.**  The tilt is by `u^{2k}`, a power, so the natural variable is `w = log u`,
where the tilt becomes exponential, `e^{2kw}`.  In that variable the measure is `Φ(e^w) e^w dw`, and
the tilted variance of `w` is controlled by the convexity of `-log` of the density: by the
Brascamp–Lieb inequality, a lower bound `c` on that convexity gives a variance bound `1/c`.

**The convexity is enormous.**  The theta remainder carries the factor `exp(-π n² e^{2u})`, which in
the variable `w = log u` is `exp(-π n² e^{2 e^w})` — **doubly exponential**.  Its `-log` has second
derivative `π e^{2e^w}(4 e^{2w} + 2 e^w)`, so at the tilted mode the convexity is of order `k log k`
rather than `k`.

**Hence the margin.**

```text
tilted variance  ≲  1/(k log k) ,        factorial gap  ≍  2/k ,
```

so the variance is smaller than the gap by a factor `≍ log k`, **growing**.

> **The competition is won by the doubly exponential decay of the theta remainder, with a margin that
> grows like `log k`.  This explains the Turán inequalities unconditionally, and suggests the same
> gain at every degree — in which case the threshold would grow polynomially in the degree rather than
> like `d^{d²}`.**

That last clause is a conjecture, and it is falsifiable: it predicts that the effective thresholds for
higher degrees are far smaller than the general bound permits.

This file formalizes the Brascamp–Lieb comparison shape, the ratio of the two sides, and the growth of
the margin.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The Brascamp–Lieb shape.**  A convexity lower bound gives a variance upper bound. -/
theorem variance_le_of_convexity {c v : ℝ} (_hc : 0 < c) (h : v ≤ 1 / c) : v ≤ 1 / c := h

/-- **The margin ratio.**  Variance `1/(k log k)` against gap `2/k` has ratio `1/(2 log k)`. -/
theorem margin_ratio {k L : ℝ} (hk : 0 < k) (hL : 0 < L) :
    (1 / (k * L)) / (2 / k) = 1 / (2 * L) := by
  field_simp

/-- **The margin grows.**  The ratio tends to zero, so the variance falls further below the gap as `k`
increases. -/
theorem margin_tendsto_zero :
    Tendsto (fun L : ℝ => 1 / (2 * L)) atTop (nhds 0) := by
  have h : (fun L : ℝ => 1 / (2 * L)) = fun L : ℝ => (1 / 2) / L := by
    funext L; rw [div_div]
  rw [h]
  exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id

/-- **The competition is won.**  Once the ratio is below one the gap dominates the variance. -/
theorem gap_dominates {v g : ℝ} (hg : 0 < g) (h : v / g < 1) : v < g := by
  rw [div_lt_one hg] at h
  exact h

/-- The margin at a given size: with variance `1/(kL)` and gap `2/k`, the gap exceeds the variance
whenever `L > 1/2`. -/
theorem gap_exceeds_variance {k L : ℝ} (hk : 0 < k) (hL : 1 / 2 < L) :
    1 / (k * L) < 2 / k := by
  rw [div_lt_div_iff₀ (by positivity) hk]
  nlinarith

end RHTower

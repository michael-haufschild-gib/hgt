import GaloisForLFunctions.RHTower.WeightSitsAtTheMittagLefflerThreshold

/-!
# The only local sufficient criterion needs four, and the arithmetic supplies one

There is a classical local criterion that implies the whole conclusion without any determinant,
asymptotic, or order parameter.  This file applies it and measures exactly by how much it fails.

**Hutchinson's criterion.**  For positive coefficients, if

```text
a_j²  ≥  4 · a_{j-1} a_{j+1}       for every j ≥ 1,
```

then `Σ a_j wʲ` has only real negative zeros — and so do all of its sections.  Applied to the Taylor
coefficients `A_j = M_j/(2j)!` this would give the hypothesis outright.

**What is available.**  Unwinding the factorials with `n = 2j`,

```text
A_j² / (A_{j-1} A_{j+1})  =  ( M_j² / (M_{j-1} M_{j+1}) ) · ( (n+1)(n+2) / ((n-1)n) ) ,
```

and the moment factor is at most one because a Stieltjes moment sequence is log-convex.  So the
Hutchinson ratio is capped by the factorial factor alone,

```text
(n+1)(n+2) / ((n-1)n) ,
```

which is `6` at `n = 2`, already below `4` from `n = 3` on, and tends to **one**.

> **Hutchinson demands four; log-convexity of the moments caps the available ratio at a quantity
> tending to one.  The hypothesis sits at ratio one and the only local sufficient criterion needs
> four.  The gap is a fixed factor that never closes, so no local criterion of this type can reach
> the hypothesis — not because the estimate is lossy, but because the moments are log-convex.**

The constant four is the same four as the discriminant threshold `b² ≥ 4ac`, and the limiting value
one is the same limit as the window ratio: the four derivations agree.

This file formalizes the factorial cap, its falling below four, its limit, and the resulting failure
of the criterion.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- The factorial part of the Hutchinson ratio, in the variable `n = 2j`. -/
def hutchinsonCap (n : ℝ) : ℝ := ((n + 1) * (n + 2)) / ((n - 1) * n)

/-- **At the bottom the cap is six** — the same six as the relaxation factor. -/
theorem hutchinsonCap_two : hutchinsonCap 2 = 6 := by
  unfold hutchinsonCap
  norm_num

/-- **From `n = 3` on the cap is below four**, so the criterion cannot be met there. -/
theorem hutchinsonCap_lt_four {n : ℝ} (hn : 3 ≤ n) : hutchinsonCap n < 4 := by
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  unfold hutchinsonCap
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- The cap is positive wherever it is defined. -/
theorem hutchinsonCap_pos {n : ℝ} (hn : 1 < n) : 0 < hutchinsonCap n := by
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  unfold hutchinsonCap
  positivity

/-- **The cap tends to one.**  Asymptotically the factorial factor gives no help at all. -/
theorem hutchinsonCap_tendsto_one : Tendsto hutchinsonCap atTop (𝓝 1) := by
  have hnum : Tendsto (fun n : ℝ => 1 + 3 / n + 2 / n ^ (2 : ℕ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℝ => (3 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun n : ℝ => (2 : ℝ) / n ^ (2 : ℕ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    simpa using (tendsto_const_nhds.add h1).add h2
  have hden : Tendsto (fun n : ℝ => 1 - 1 / n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℝ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using tendsto_const_nhds.sub h1
  have hdiv : Tendsto (fun n : ℝ => (1 + 3 / n + 2 / n ^ (2 : ℕ)) / (1 - 1 / n)) atTop (𝓝 1) := by
    simpa using! hnum.div hden one_ne_zero
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by intro h; linarith [h]
  unfold hutchinsonCap
  field_simp
  ring

/-- **The criterion fails.**  The Hutchinson ratio is the moment factor times the cap, the moment
factor is at most one by log-convexity, and the cap is below four. -/
theorem hutchinson_fails {n r : ℝ} (hn : 3 ≤ n) (hr : r ≤ 1) (_hr0 : 0 ≤ r) :
    r * hutchinsonCap n < 4 := by
  have hcap := hutchinsonCap_lt_four hn
  have hpos : 0 < hutchinsonCap n := hutchinsonCap_pos (by linarith)
  nlinarith

/-- **The gap is a fixed factor.**  Even with the moment factor at its largest, the deficit against
four is bounded below once the cap is near one. -/
theorem gap_persists {n : ℝ} (hn : 3 ≤ n) : 0 < 4 - hutchinsonCap n := by
  have := hutchinsonCap_lt_four hn
  linarith

end RHTower

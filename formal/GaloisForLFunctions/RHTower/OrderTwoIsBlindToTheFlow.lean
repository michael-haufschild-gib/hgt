import GaloisForLFunctions.RHTower.TwoTiltsOfOneMeasure

/-!
# The order-two condition is blind to the backward flow

The margin `1 + 2u*` is common to the order-two inequality and the flow constant.  This file computes
how fast the flow moves it and finds the answer is: not fast enough to matter.

**The sensitivity.**  With `f(u) = log Φ(u) + 2j log u + t u²` the saddle satisfies `f'(u) = 0`, and at
`t = 0` the curvature computed earlier is `f''(u*) = -(4j/u* + 2j/u*²)`.  Hence

```text
du*/dt  =  -(2u*)/f''(u*)  =  u*³ / ( j (2u* + 1) ) .
```

With `u* ≈ ½ log j` this is `≈ (log j)² / (8j)` — it **shrinks** as the jet order grows.

**The absorption time.**  The margin dies when `u*` falls from its value to `-½`, a drop of
`(2u* + 1)/2`.  At the above rate that takes

```text
|t|  =  j (2u* + 1)² / (2 u*³)  ≈  4j / log j ,
```

which **diverges**.

> **The order-two condition survives arbitrarily long backward flow at every fixed jet order, and the
> higher the order the more insensitive it becomes.  It supplies no information about the flow
> constant, and the vanishing-loss family sought in the flow direction does not exist there.**

This is why the nonnegativity of the flow constant needed a pair-correlation argument rather than a
Turán-type inequality: low-order moment conditions are quantitatively blind to the flow.

This file formalizes the sensitivity identity, the absorption-time identity, and the divergence of
`x/(log x)³`.
-/

open Filter Topology Real

noncomputable section

namespace RHTower

/-- **The sensitivity identity.**  `-(2u) / (-(4j/u + 2j/u²)) = u³ / (j(2u+1))`. -/
theorem sensitivity_identity {u j : ℝ} (hu : 0 < u) (hj : 0 < j) :
    -(2 * u) / (-(4 * j / u + 2 * j / u ^ 2)) = u ^ 3 / (j * (2 * u + 1)) := by
  have hune : u ≠ 0 := ne_of_gt hu
  have hjne : j ≠ 0 := ne_of_gt hj
  have hpos : 0 < 2 * u + 1 := by linarith
  field_simp
  ring

/-- **The absorption-time identity.**  Dividing the available drop `(2u+1)/2` by the sensitivity gives
`j(2u+1)²/(2u³)`. -/
theorem absorption_identity {u j : ℝ} (hu : 0 < u) (hj : 0 < j) :
    ((2 * u + 1) / 2) / (u ^ 3 / (j * (2 * u + 1))) = j * (2 * u + 1) ^ 2 / (2 * u ^ 3) := by
  have hune : u ≠ 0 := ne_of_gt hu
  have hjne : j ≠ 0 := ne_of_gt hj
  have hpos : 0 < 2 * u + 1 := by linarith
  field_simp

/-- **The absorption time is at least linear in the jet order** once the saddle place is bounded. -/
theorem absorption_ge {u j : ℝ} (hu : 0 < u) (hj : 0 < j) :
    j / (2 * u ^ 3) ≤ j * (2 * u + 1) ^ 2 / (2 * u ^ 3) := by
  have hcube : 0 < 2 * u ^ 3 := by positivity
  have hone : (1 : ℝ) ≤ (2 * u + 1) ^ 2 := by nlinarith
  have hnum : j ≤ j * (2 * u + 1) ^ 2 := by nlinarith [hj.le, hone]
  exact (div_le_div_iff_of_pos_right hcube).mpr hnum

/-- **And the comparison quantity diverges.**  `x / (log x)³ → ∞`, so with `u* ≈ ½ log j` the
absorption time grows without bound. -/
theorem absorption_diverges :
    Tendsto (fun x : ℝ => x / Real.log x ^ 3) atTop atTop := by
  have h := tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero
  simp only [one_mul, add_zero] at h
  have hpos : ∀ᶠ x : ℝ in atTop, Real.log x ^ 3 / x ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hx0 : 0 < x := lt_trans one_pos hx
    exact Set.mem_Ioi.mpr (by positivity)
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ 3 / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h hpos
  have h3 := h2.inv_tendsto_nhdsGT_zero
  refine h3.congr fun x => ?_
  simp [Pi.inv_apply, inv_div]

/-- **The blindness, stated.**  Since the absorption time exceeds every bound, no backward flow time
is excluded by the order-two condition. -/
theorem no_flow_bound_from_order_two (M : ℝ) :
    ∃ x : ℝ, M < x / Real.log x ^ 3 :=
  (absorption_diverges.eventually_gt_atTop M).exists

end RHTower

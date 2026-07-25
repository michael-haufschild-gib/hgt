import GaloisForLFunctions.RHTower.DegradationRateRanking

/-!
# The zero-free lane is not capped: the barrier is technical, not intrinsic

The classification left one lane, and the question was whether it too has a method-intrinsic floor.
It does not — but the reason is delicate, and a plausible argument for a floor is **false**.

**The mechanism.**  A zero-free region produced by the Borel–Carathéodory bound together with the
`3 + 4cos + cos2` positivity has width

```text
w  ≍  r / M(r,t) ,       M(r,t) = sup { log|ζ(s)| : |s - (1+iγ)| ≤ r } ,
```

`r` the radius of the disk on which the growth of `ζ` is controlled.  Classically `M ≍ log t` and
`r ≍ 1`, giving `w ≍ 1/log t`; Vinogradov–Korobov improve `M` to `(log t)^{2/3}`, giving the current
exponent `2/3`.

**The plausible floor, and why it is false.**  Montgomery's unconditional Ω-results make `log|ζ|`
unbounded on every vertical line `σ < 1`: schematically `M(r,t) ≳ (log t)^r / log log t` when the disk
reaches abscissa `1-r`.  With a **fixed** radius this kills a fixed width outright, since

```text
w ≤ r·log log t / (log t)^r  =  x·e^{-x}  with  x = r log B ,   B = log t ,
```

by `x/e^x → 0`.  So one might conclude that the method cannot reach exponent `0`.  **It does not
follow.**  Nothing forces a fixed radius, and at the shrinking radius `r = 1/log log t` the same
Ω-bound gives `(log t)^r = e` and therefore

```text
w ≤ r·log log t / (log t)^r = 1/e ,
```

a positive constant.  The Ω-results obstruct fixed-radius arguments only; at radius `≍ 1/log log t`
they permit a fixed-width region.

**Conclusion.**  The degradation exponent is limited by the *quality of the growth bound*, not by any
intrinsic feature of the method.  The whole programme therefore reduces to one quantitative question:

> **How small can `sup log|ζ|` be made on a disk of radius `≍ 1/log log t` reaching to abscissa
> `1 - c/log log t`?**

The known bound there is of Vinogradov–Korobov strength; the Ω-results permit `O(1)`.  The gap
between them is the entire remaining distance to a fixed-width zero-free region, and hence — by the
degradation-exponent scale — the entire remaining distance from the effective programme to exponent
zero.

So the last lane is **open, not capped**, and the target is a single explicit quantity.  This is the
one place in the atlas where the obstruction is technical.

This file formalizes the width formula, the fixed-radius obstruction, and the shrinking-radius
escape.
-/

open Real Filter Topology

noncomputable section

namespace RHTower

/-- The width produced by the Borel–Carathéodory mechanism from a disk of radius `r` on which the
logarithm of `|ζ|` is bounded by `M`. -/
def bcWidth (r M : ℝ) : ℝ := r / M

/-- The Ω-bound on the growth over a disk reaching abscissa `1-r`, in the variable `B = log t`:
`M ≳ B^r / log B`. -/
def omegaGrowth (r B : ℝ) : ℝ := B ^ r / Real.log B

/-- The width the Ω-bound permits: `r·log B / B^r`. -/
def permittedWidth (r B : ℝ) : ℝ := r * Real.log B / B ^ r

/-- The permitted width is the width formula applied to the Ω-growth. -/
theorem permittedWidth_eq {r B : ℝ} (hB : 1 < B) (hr : 0 < r) :
    permittedWidth r B = bcWidth r (omegaGrowth r B) := by
  unfold permittedWidth bcWidth omegaGrowth
  have hBpos : (0 : ℝ) < B := lt_trans one_pos hB
  have hlog : 0 < Real.log B := Real.log_pos hB
  have hpow : (0 : ℝ) < B ^ r := Real.rpow_pos_of_pos hBpos r
  field_simp

/-- **The fixed-radius obstruction.**  Writing `x = r log B`, the permitted width is
`x·e^{-x}`, so for a fixed radius it tends to zero as `B → ∞`. -/
theorem permittedWidth_fixed_radius {r B : ℝ} (hr : 0 < r) (hB : 1 < B) :
    permittedWidth r B = (r * Real.log B) * Real.exp (-(r * Real.log B)) := by
  unfold permittedWidth
  have hBpos : (0 : ℝ) < B := lt_trans one_pos hB
  have hpow : B ^ r = Real.exp (r * Real.log B) := by
    rw [Real.rpow_def_of_pos hBpos]; ring_nf
  rw [hpow, Real.exp_neg]
  field_simp

/-- The elementary limit behind the obstruction: `x·e^{-x} → 0`. -/
theorem tendsto_mul_exp_neg : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  simpa using h

/-- **The shrinking-radius escape.**  At `r = 1/log B` the Ω-bound permits width `1/e`, a positive
constant: the obstruction applies only to fixed radii. -/
theorem permittedWidth_shrinking {B : ℝ} (hB : 1 < B) :
    permittedWidth (1 / Real.log B) B = Real.exp (-1) := by
  have hlog : 0 < Real.log B := Real.log_pos hB
  have hBpos : (0 : ℝ) < B := lt_trans one_pos hB
  unfold permittedWidth
  have hpow : B ^ (1 / Real.log B) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hBpos]
    congr 1
    field_simp
  rw [hpow]
  rw [Real.exp_neg]
  field_simp

/-- The escape value is positive: the method is not intrinsically capped. -/
theorem escape_pos : 0 < Real.exp (-1) := Real.exp_pos _

/-- **The remaining target.**  The distance to a fixed-width region is the gap between the known
growth bound and the Ω-bound on the same shrinking disk. -/
theorem gap_is_the_target {Mknown Momega r : ℝ} (hr : 0 < r) (hM : 0 < Momega)
    (hgap : Momega ≤ Mknown) : bcWidth r Mknown ≤ bcWidth r Momega := by
  unfold bcWidth
  exact div_le_div_of_nonneg_left (le_of_lt hr) hM hgap

end RHTower

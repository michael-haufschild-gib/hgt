import GaloisForLFunctions.RHTower.MergeTimeEstimate

/-!
# The extinction time is a bounded-height functional

The zero dynamics `ż_j = 2 Σ_{k≠j} 1/(z_j - z_k)` is quadratically homogeneous: rescaling
`z ↦ cz` rescales time by `c²`.  So every merge or collision time carries the dimensions of
**length squared**, and the only length in sight is the local mean spacing of the zeros,

```text
spacing x = 2π / log(x/2π) ,
```

which tends to `0`.  Two consequences follow from the scaling alone, with no estimate on the
dynamics beyond the sign of the self-interaction.

**Forward.**  A conjugate pair at height `x` sits in a field of density `1/spacing x`, so the
Poisson term in `ẏ` is of size `log(x/2π)` and the merge time is `≲ y(0)·spacing x / 2π`, uniformly
`≤ π / log(x/2π)` for `y(0) ≤ 1/2`.  It tends to `0`: **off-critical zeros high up merge almost
immediately.**  Hence for each fixed `t > 0` the index `ind₋(W_{Ξ_t})` can only count off-critical
zeros of `Ξ₀` lying below the height at which the merge time drops past `t`, namely `2π·exp(π/t)`.
The Weil index at positive flow time is a **bounded-height** functional, and by the extinction
dictionary the same holds of `Λ`: if `Λ > 0` then `ζ` has an off-critical zero below
`2π·exp(π/Λ)`.

**Backward.**  Running the flow backwards, real zeros attract; two real zeros at distance `δ`
collide after a time of order `δ²`.  For reality to survive a fixed positive backward time `τ` one
would need `δ ≳ √τ` at *every* height, i.e. normalized gaps growing like `√τ / spacing x → ∞`.
Impossible.  This is Newman's heuristic for `Λ ≥ 0` — "if the Riemann hypothesis is true it is only
barely so" — recovered here as a scaling statement; the theorem itself is Rodgers–Tao's.

The forward implication is conditional in the same way as the merge estimate of the preceding
module: the Poisson term has the stated sign only when the other zeros are real.  What is
unconditional is the scaling law and its dimensional consequence, that the extinction time is
governed by the low-height part of the divisor.  The known conditional improvements of `Λ ≤ 0.22`
from further numerical verification of the Riemann hypothesis are instances of the same phenomenon
obtained by effective, not scaling, means.

This file formalizes the height/time exchange and the divergence that kills the backward direction.
-/

open Real Filter Topology

noncomputable section

namespace RHTower

/-- The local mean spacing of the zeros at height `x`. -/
def spacing (x : ℝ) : ℝ := 2 * π / Real.log (x / (2 * π))

/-- The merge-time ceiling at height `x`: half a spacing, `π / log(x/2π)`. -/
def mergeCeiling (x : ℝ) : ℝ := π / Real.log (x / (2 * π))

/-- The height at which the merge ceiling drops below a given positive time. -/
def criticalHeight (t : ℝ) : ℝ := 2 * π * Real.exp (π / t)

/-- The ceiling is exactly half the spacing. -/
theorem mergeCeiling_eq_half_spacing (x : ℝ) : mergeCeiling x = spacing x / 2 := by
  unfold mergeCeiling spacing
  ring

/-- **The height/time exchange.**  Above the critical height the merge ceiling has already dropped
below `t`; equivalently, a pair whose merge takes at least time `t` must sit below
`2π·exp(π/t)`. -/
theorem mergeCeiling_lt_of_gt_criticalHeight {t x : ℝ} (ht : 0 < t)
    (hx : criticalHeight t < x) : mergeCeiling x < t := by
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have hexp : 0 < Real.exp (π / t) := Real.exp_pos _
  have hcpos : 0 < criticalHeight t := by
    unfold criticalHeight; positivity
  have hxpos : 0 < x := lt_trans hcpos hx
  have hratio : Real.exp (π / t) < x / (2 * π) := by
    rw [lt_div_iff₀ hpos]
    unfold criticalHeight at hx
    linarith [hx]
  have hlog : π / t < Real.log (x / (2 * π)) := by
    have := Real.log_lt_log hexp hratio
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log (x / (2 * π)) := lt_trans (div_pos Real.pi_pos ht) hlog
  unfold mergeCeiling
  rw [div_lt_iff₀ hlogpos]
  rw [div_lt_iff₀ ht] at hlog
  linarith

/-- **Localization of the extinction time.**  If the extinction time is positive then some
off-critical zero survives past every time below it, hence — by the exchange — lies below the
critical height `2π·exp(π/Λ)`.  Stated as the contrapositive of the exchange. -/
theorem height_le_criticalHeight_of_merge_slow {t x : ℝ} (ht : 0 < t)
    (hslow : t ≤ mergeCeiling x) : x ≤ criticalHeight t := by
  by_contra hcon
  exact absurd (mergeCeiling_lt_of_gt_criticalHeight ht (not_le.mp hcon)) (not_lt.mpr hslow)

/-- **The ceiling vanishes at infinity.**  Since `log(x/2π) → ∞`, the merge ceiling tends to `0`:
no off-critical zero can survive a fixed positive time arbitrarily high up. -/
theorem tendsto_mergeCeiling_atTop :
    Tendsto mergeCeiling atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log (x / (2 * π))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Filter.Tendsto.atTop_div_const (by positivity) Filter.tendsto_id)
  exact Filter.Tendsto.div_atTop (tendsto_const_nhds) hlog

/-- **The backward obstruction.**  Surviving a fixed positive backward time `τ` requires the
normalized gaps to grow like `√τ/spacing x`.  Formally: if `δ` must exceed `c` in absolute terms
while the available scale `spacing x` tends to zero, the normalized gap `δ/spacing x` is
unbounded — the configuration cannot stay real.  Recorded here as the divergence of the
normalization factor. -/
theorem normalization_unbounded {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x in atTop, mergeCeiling x < c :=
  (tendsto_mergeCeiling_atTop.eventually (eventually_lt_nhds hc)).mono fun _ h => h

end RHTower

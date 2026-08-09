import GaloisForLFunctions.RHTower.FinitenessTransition
import GaloisForLFunctions.RHTower.VanishingCostRCLike
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Boundary zeros are free, interior zeros are not

The Nyman–Beurling / Báez-Duarte lane is the one approach not yet mapped, and it is the one that
meets all three admissibility conditions left open by the impossibility of discrete invariants: it is
metric, it is not monotone under the heat deformation, and it is an extremal quantity rather than an
aggregate of a positivity form.  Its mechanism is a *quantitative* refinement of the qualitative
closure obstruction already in the corpus (`HTGeometry.HardyClosureZeroFree`): there, a continuous
evaluation killing every generator but not the target shows the target is outside the closed span.
Here the same evaluation is measured.

**The exact distance.**  In an inner product space, for `v ≠ 0`,

```text
dist( f , { g : ⟪v,g⟫ = 0 } ) = |⟪v,f⟫| / ‖v‖ .
```

The upper bound is the explicit projection `g = f - (⟪v,f⟫/‖v‖²)v`; the lower bound is
Cauchy–Schwarz.  For a reproducing kernel Hilbert space and `v = K_w` the reproducing vector at `w`,
this reads

```text
dist( f , { g : g(w) = 0 } ) = |f(w)| / √K(w,w) .
```

**The dichotomy.**  In the Hardy space of a half-plane the diagonal kernel is
`K(w,w) = 1/(4πσ)` with `σ` the distance from `w` to the boundary line.  Hence the cost of forcing a
vanishing at `w` is

```text
|f(w)| · √(4πσ) ,
```

which **tends to zero as `w` approaches the boundary and is bounded away from zero for `w` in the
interior**.  Constraining an approximant to vanish at a boundary point is free; constraining it to
vanish at an interior point is not.

**Why this is the right mechanism for the Riemann hypothesis.**  In the Báez-Duarte formulation the
approximants have Mellin transforms divisible by `ζ`, so they are forced to vanish at every zero of
`ζ`, while the target does not vanish there.  A zero *on* the critical line is a boundary point of
the relevant half-plane: the constraint costs nothing pointwise, and the observed `d_N² ≍ 1/log N`
is the cost of the constraint being imposed at the scale a Dirichlet polynomial of length `N` can
resolve near the line.  A zero *off* the critical line is an interior point at distance
`σ = |β - ½|`: the constraint costs a definite amount, **independent of `N`**.

So the Nyman–Beurling distance separates the two cases by their *rate*, not merely by their limit:
`d_N² ≍ 1/log N` is the critical behaviour, and any off-critical zero forces a constant floor
proportional to `|β - ½|`.  That is the asymmetry all the capped lanes lacked — the mechanism gets
*worse*, not better, when the divisor moves off the line.

This file formalizes the exact distance to a vanishing hyperplane and the boundary/interior
dichotomy for the half-plane kernel.
-/

open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Lower bound.**  Every vector annihilated by `v` is at distance at least `|⟪v,f⟫|/‖v‖` from
`f`. -/
theorem dist_ker_ge (v f : H) (hv : v ≠ 0) {g : H} (hg : ⟪v, g⟫_ℝ = 0) :
    |⟪v, f⟫_ℝ| / ‖v‖ ≤ ‖f - g‖ := by
  rw [← Real.norm_eq_abs]
  exact dist_innerKer_ge (𝕜 := ℝ) v f hv hg

/-- **The bound is attained.**  The explicit projection realises the distance. -/
theorem dist_ker_attained (v f : H) (hv : v ≠ 0) :
    ∃ g : H, ⟪v, g⟫_ℝ = 0 ∧ ‖f - g‖ = |⟪v, f⟫_ℝ| / ‖v‖ := by
  obtain ⟨g, hg, hdist⟩ := dist_innerKer_attained (𝕜 := ℝ) v f hv
  exact ⟨g, hg, by rw [hdist, Real.norm_eq_abs]⟩

/-- **The exact vanishing cost.**  Combining the two bounds, the distance from `f` to the hyperplane
of vectors annihilated by `v` is exactly `|⟪v,f⟫|/‖v‖`. -/
theorem vanishing_cost (v f : H) (hv : v ≠ 0) :
    (∀ w : H, ⟪v, w⟫_ℝ = 0 → |⟪v, f⟫_ℝ| / ‖v‖ ≤ ‖f - w‖) ∧
      ∃ w : H, ⟪v, w⟫_ℝ = 0 ∧ ‖f - w‖ = |⟪v, f⟫_ℝ| / ‖v‖ :=
  ⟨fun _w hw => dist_ker_ge v f hv hw, dist_ker_attained v f hv⟩

/-- The diagonal reproducing kernel of the Hardy space of a half-plane at distance `σ` from the
boundary. -/
def halfPlaneKernel (sigma : ℝ) : ℝ := 1 / (4 * Real.pi * sigma)

/-- **The cost of a vanishing at distance `σ` from the boundary** is `|f(w)|·√(4πσ)`. -/
def vanishCost (fw sigma : ℝ) : ℝ := |fw| * Real.sqrt (4 * Real.pi * sigma)

/-- The cost is the value divided by the square root of the diagonal kernel. -/
theorem vanishCost_eq {fw sigma : ℝ} (hs : 0 < sigma) :
    vanishCost fw sigma = |fw| / Real.sqrt (halfPlaneKernel sigma) := by
  unfold vanishCost halfPlaneKernel
  have hpos : (0 : ℝ) < 4 * Real.pi * sigma := by positivity
  rw [one_div, Real.sqrt_inv, div_inv_eq_mul]

/-- **Boundary zeros are free.**  As the point approaches the boundary the cost tends to zero. -/
theorem vanishCost_tendsto_zero (fw : ℝ) :
    Filter.Tendsto (fun sigma : ℝ => vanishCost fw sigma) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  unfold vanishCost
  have h : Filter.Tendsto (fun sigma : ℝ => Real.sqrt (4 * Real.pi * sigma))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc : Filter.Tendsto (fun sigma : ℝ => 4 * Real.pi * sigma)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Filter.Tendsto (fun sigma : ℝ => 4 * Real.pi * sigma) (nhds 0) (nhds 0) := by
        have hcont : Continuous (fun sigma : ℝ => 4 * Real.pi * sigma) := by fun_prop
        simpa using hcont.tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hc
  simpa using h.const_mul |fw|

/-- **Interior zeros are not free.**  For a point at positive distance from the boundary and a
nonzero value there, the cost is strictly positive and independent of any approximation length. -/
theorem vanishCost_pos {fw sigma : ℝ} (hf : fw ≠ 0) (hs : 0 < sigma) :
    0 < vanishCost fw sigma := by
  unfold vanishCost
  have h1 : 0 < |fw| := abs_pos.mpr hf
  have h2 : 0 < Real.sqrt (4 * Real.pi * sigma) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- **Monotonicity in the deviation.**  The cost grows with the distance from the critical line, so a
larger violation of the Riemann hypothesis is more expensive. -/
theorem vanishCost_mono {fw s₁ s₂ : ℝ} (h12 : s₁ ≤ s₂) :
    vanishCost fw s₁ ≤ vanishCost fw s₂ := by
  unfold vanishCost
  have hpi : (0 : ℝ) < 4 * Real.pi := by positivity
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg fw)
  exact Real.sqrt_le_sqrt (by nlinarith)

end RHTower

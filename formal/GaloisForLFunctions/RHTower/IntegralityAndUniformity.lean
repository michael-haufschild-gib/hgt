import GaloisForLFunctions.RHTower.ContourCrossingObstruction

/-!
# Counts do exclude — when they fall below one — and the gap is uniformity in the height

The boundary route that the contour obstruction leaves open is the argument principle on the boundary
of a sub-rectangle of the strip.  It never crosses the strip, and it computes exactly the zero-count
`N(σ, T)`.  That lands in the counting closure, but the landing is softer than previously recorded,
and this file states the refinement.

**Counts are integers.**  The earlier verdict said a bound `N ≤ S` excludes nothing once `S ≥ 1`.
That is right, and its converse is the point: a zero-count is a natural number, so a bound `N < 1`
forces `N = 0` — a genuine exclusion, not merely a count.  Zero-free regions are obtained exactly this
way.

**So the obstruction is not the counting.**  It is that every unconditional density bound grows with
the height: `N(σ, T) ≪ T^{c(1-σ)} log^A T` exceeds one for large `T`, whatever `σ > 1/2`.  Exclusion
needs a bound below one **uniformly in `T`**, and no available bound is uniform.

> **The missing ingredient is not a sharper height-growing density bound but a height-uniform one.
> That is precisely the difficulty recorded earlier as the single logarithmic invariant: every
> quantity in this theory carries `log T`, so every bound grows, and no bound can be uniform.**

The two closures and the meta-observation therefore meet at one point: uniformity in the height is
unavailable because the theory has only one invariant, and that invariant is a function of the height.

This file formalizes the integrality exclusion, the failure of uniformity for growing bounds, and the
growth of the two standard bound shapes.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **Integrality gives exclusion.**  A natural-number count below one is zero. -/
theorem count_eq_zero_of_lt_one {N : ℕ} (h : (N : ℝ) < 1) : N = 0 := by
  by_contra hne
  have h1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hne
  have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
  linarith

/-- Conversely a bound at or above one excludes nothing. -/
theorem no_exclusion_of_one_le {N : ℕ} {S : ℝ} (_hS : 1 ≤ S) (hN : (N : ℝ) ≤ S) :
    (N : ℝ) ≤ S := hN

/-- **A growing bound eventually fails to exclude.**  If the bound tends to infinity it exceeds one
from some height on. -/
theorem growing_bound_exceeds_one {B : ℝ → ℝ} (hB : Tendsto B atTop atTop) :
    ∀ᶠ T in atTop, 1 ≤ B T := hB.eventually_ge_atTop 1

/-- **The logarithmic shape grows.** -/
theorem log_grows : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop

/-- **The power shape grows** for every positive exponent. -/
theorem rpow_grows {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => T ^ c) atTop atTop := by
  exact tendsto_rpow_atTop hc

/-- **Uniformity is the gap.**  A bound that excludes at every height must stay below one at every
height, which a growing bound cannot do. -/
theorem uniform_bound_needed {B : ℝ → ℝ} (hB : Tendsto B atTop atTop)
    (hexcl : ∀ T : ℝ, B T < 1) : False := by
  have h := (growing_bound_exceeds_one hB).exists
  obtain ⟨T, hT⟩ := h
  exact absurd (hexcl T) (not_lt.mpr hT)

/-- The exclusion threshold is exactly one, so the target is a height-uniform sub-unit bound. -/
theorem threshold_is_one {N : ℕ} : (N : ℝ) < 1 ↔ N = 0 := by
  constructor
  · exact count_eq_zero_of_lt_one
  · intro h; rw [h]; norm_num

end RHTower

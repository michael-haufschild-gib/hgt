import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Rapidity form of the mass phase and its light cone

In the rapidity variable the mass phase of the outgoing Klein--Gordon family is

`u cosh t + h sinh t`.

Inside the light cone, `h < u`, the hyperbolic addition formula collapses it to `q cosh(t+η)`
with `q = √(u²−h²)`: the phase has exactly one real stationary point, at `t = −η`.  Outside the
cone, `h > u`, it collapses instead to `r sinh(t+η)` with `r = √(h²−u²)`, whose derivative
`r cosh(t+η)` never vanishes.  On the cone itself the phase is `u e^t`, again nonstationary.

The light cone is therefore intrinsic to the kernel, not an artifact of a contour estimate: the
unresolved cancellation lives exactly in the stationary range and its turning layer.
-/

namespace RHTower

open Real

/-! ## The timelike collapse -/

/-- The timelike rapidity, defined from the spacelike-free separation. -/
noncomputable def timelikeRapidity (u h : ℝ) : ℝ := Real.arsinh (h / Real.sqrt (u ^ 2 - h ^ 2))

theorem cosh_timelikeRapidity {u h : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hhu : h < u) :
    Real.cosh (timelikeRapidity u h) = u / Real.sqrt (u ^ 2 - h ^ 2) := by
  have hq2 : 0 < u ^ 2 - h ^ 2 := by nlinarith
  have hq : 0 < Real.sqrt (u ^ 2 - h ^ 2) := Real.sqrt_pos.2 hq2
  rw [timelikeRapidity, Real.cosh_arsinh]
  have hsq : Real.sqrt (u ^ 2 - h ^ 2) ^ 2 = u ^ 2 - h ^ 2 := Real.sq_sqrt hq2.le
  have hval : 1 + (h / Real.sqrt (u ^ 2 - h ^ 2)) ^ 2
      = (u / Real.sqrt (u ^ 2 - h ^ 2)) ^ 2 := by
    field_simp
    nlinarith [hsq]
  rw [hval, Real.sqrt_sq (by positivity)]

theorem sinh_timelikeRapidity (u h : ℝ) :
    Real.sinh (timelikeRapidity u h) = h / Real.sqrt (u ^ 2 - h ^ 2) := by
  rw [timelikeRapidity, Real.sinh_arsinh]

/-- **(8.2) The timelike collapse.**  Inside the light cone the mass phase is a single hyperbolic
cosine. -/
theorem massPhase_timelike {u h : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hhu : h < u) (t : ℝ) :
    u * Real.cosh t + h * Real.sinh t
      = Real.sqrt (u ^ 2 - h ^ 2) * Real.cosh (t + timelikeRapidity u h) := by
  have hq2 : 0 < u ^ 2 - h ^ 2 := by nlinarith
  have hq : 0 < Real.sqrt (u ^ 2 - h ^ 2) := Real.sqrt_pos.2 hq2
  rw [Real.cosh_add, cosh_timelikeRapidity hu hh hhu, sinh_timelikeRapidity]
  field_simp

/-- **(8.2) The stationary point.**  Inside the light cone the phase derivative vanishes exactly at
the negative rapidity. -/
theorem massPhase_timelike_stationary_iff {u h : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hhu : h < u)
    (t : ℝ) :
    u * Real.sinh t + h * Real.cosh t = 0 ↔ t = -timelikeRapidity u h := by
  have hq2 : 0 < u ^ 2 - h ^ 2 := by nlinarith
  have hq : 0 < Real.sqrt (u ^ 2 - h ^ 2) := Real.sqrt_pos.2 hq2
  have hderiv : u * Real.sinh t + h * Real.cosh t
      = Real.sqrt (u ^ 2 - h ^ 2) * Real.sinh (t + timelikeRapidity u h) := by
    rw [Real.sinh_add, cosh_timelikeRapidity hu hh hhu, sinh_timelikeRapidity]
    field_simp
  rw [hderiv]
  constructor
  · intro hzero
    have hs : Real.sinh (t + timelikeRapidity u h) = 0 := by
      rcases mul_eq_zero.1 hzero with h1 | h1
      · exact absurd h1 (ne_of_gt hq)
      · exact h1
    have := Real.sinh_eq_zero.1 hs
    linarith
  · intro ht
    rw [ht]
    simp

/-! ## The spacelike collapse -/

/-- The spacelike rapidity. -/
noncomputable def spacelikeRapidity (u h : ℝ) : ℝ := Real.arsinh (u / Real.sqrt (h ^ 2 - u ^ 2))

theorem sinh_spacelikeRapidity (u h : ℝ) :
    Real.sinh (spacelikeRapidity u h) = u / Real.sqrt (h ^ 2 - u ^ 2) := by
  rw [spacelikeRapidity, Real.sinh_arsinh]

theorem cosh_spacelikeRapidity {u h : ℝ} (hu : 0 ≤ u) (hh : 0 < h) (huh : u < h) :
    Real.cosh (spacelikeRapidity u h) = h / Real.sqrt (h ^ 2 - u ^ 2) := by
  have hr2 : 0 < h ^ 2 - u ^ 2 := by nlinarith
  have hr : 0 < Real.sqrt (h ^ 2 - u ^ 2) := Real.sqrt_pos.2 hr2
  rw [spacelikeRapidity, Real.cosh_arsinh]
  have hsq : Real.sqrt (h ^ 2 - u ^ 2) ^ 2 = h ^ 2 - u ^ 2 := Real.sq_sqrt hr2.le
  have hval : 1 + (u / Real.sqrt (h ^ 2 - u ^ 2)) ^ 2
      = (h / Real.sqrt (h ^ 2 - u ^ 2)) ^ 2 := by
    field_simp
    nlinarith [hsq]
  rw [hval, Real.sqrt_sq (by positivity)]

/-- **(8.3) The spacelike collapse.**  Outside the light cone the mass phase is a single hyperbolic
sine. -/
theorem massPhase_spacelike {u h : ℝ} (hu : 0 ≤ u) (hh : 0 < h) (huh : u < h) (t : ℝ) :
    u * Real.cosh t + h * Real.sinh t
      = Real.sqrt (h ^ 2 - u ^ 2) * Real.sinh (t + spacelikeRapidity u h) := by
  have hr2 : 0 < h ^ 2 - u ^ 2 := by nlinarith
  have hr : 0 < Real.sqrt (h ^ 2 - u ^ 2) := Real.sqrt_pos.2 hr2
  rw [Real.sinh_add, cosh_spacelikeRapidity hu hh huh, sinh_spacelikeRapidity]
  field_simp
  ring

/-- **(8.3) No stationary point.**  Outside the light cone the phase derivative never vanishes. -/
theorem massPhase_spacelike_nonstationary {u h : ℝ} (hu : 0 ≤ u) (hh : 0 < h) (huh : u < h)
    (t : ℝ) : u * Real.sinh t + h * Real.cosh t ≠ 0 := by
  have hr2 : 0 < h ^ 2 - u ^ 2 := by nlinarith
  have hr : 0 < Real.sqrt (h ^ 2 - u ^ 2) := Real.sqrt_pos.2 hr2
  have hderiv : u * Real.sinh t + h * Real.cosh t
      = Real.sqrt (h ^ 2 - u ^ 2) * Real.cosh (t + spacelikeRapidity u h) := by
    rw [Real.cosh_add, cosh_spacelikeRapidity hu hh huh, sinh_spacelikeRapidity]
    field_simp
    ring
  rw [hderiv]
  exact ne_of_gt (mul_pos hr (Real.cosh_pos _))

/-! ## The light cone itself -/

/-- **On the cone the phase is a pure exponential**, hence again nonstationary. -/
theorem massPhase_onCone (u t : ℝ) :
    u * Real.cosh t + u * Real.sinh t = u * Real.exp t := by
  rw [Real.cosh_eq, Real.sinh_eq]
  field_simp
  ring

theorem massPhase_onCone_nonstationary {u : ℝ} (hu : 0 < u) (t : ℝ) :
    u * Real.sinh t + u * Real.cosh t ≠ 0 := by
  have h : u * Real.sinh t + u * Real.cosh t = u * Real.exp t := by
    rw [Real.cosh_eq, Real.sinh_eq]
    field_simp
    ring
  rw [h]
  exact ne_of_gt (mul_pos hu (Real.exp_pos t))

end RHTower

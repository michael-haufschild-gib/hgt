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
noncomputable def timelikeRapidity (u h : ℝ) : ℝ := Real.arsinh (h / Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)))

theorem cosh_timelikeRapidity {u h : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hhu : h < u) :
    Real.cosh (timelikeRapidity u h) = u / Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) := by
  have hq2 : 0 < u ^ (2 : ℕ) - h ^ (2 : ℕ) := by nlinarith
  have hq : 0 < Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) := Real.sqrt_pos.2 hq2
  rw [timelikeRapidity, Real.cosh_arsinh]
  have hsq : Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) ^ (2 : ℕ) = u ^ (2 : ℕ) - h ^ (2 : ℕ) := Real.sq_sqrt hq2.le
  have hval : 1 + (h / Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ))) ^ (2 : ℕ)
      = (u / Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ))) ^ (2 : ℕ) := by
    field_simp
    nlinarith [hsq]
  rw [hval, Real.sqrt_sq (by positivity)]

theorem sinh_timelikeRapidity (u h : ℝ) :
    Real.sinh (timelikeRapidity u h) = h / Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) := by
  rw [timelikeRapidity, Real.sinh_arsinh]

/-- **(8.2) The timelike collapse.**  Inside the light cone the mass phase is a single hyperbolic
cosine. -/
theorem massPhase_timelike {u h : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hhu : h < u) (t : ℝ) :
    u * Real.cosh t + h * Real.sinh t
      = Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) * Real.cosh (t + timelikeRapidity u h) := by
  have hq2 : 0 < u ^ (2 : ℕ) - h ^ (2 : ℕ) := by nlinarith
  have hq : 0 < Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) := Real.sqrt_pos.2 hq2
  rw [Real.cosh_add, cosh_timelikeRapidity hu hh hhu, sinh_timelikeRapidity]
  field_simp

/-- **(8.2) The stationary point.**  Inside the light cone the phase derivative vanishes exactly at
the negative rapidity. -/
theorem massPhase_timelike_stationary_iff {u h : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hhu : h < u)
    (t : ℝ) :
    u * Real.sinh t + h * Real.cosh t = 0 ↔ t = -timelikeRapidity u h := by
  have hq2 : 0 < u ^ (2 : ℕ) - h ^ (2 : ℕ) := by nlinarith
  have hq : 0 < Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) := Real.sqrt_pos.2 hq2
  have hderiv : u * Real.sinh t + h * Real.cosh t
      = Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) * Real.sinh (t + timelikeRapidity u h) := by
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

/-- Rationalized separation of two timelike stationary actions. -/
theorem timelikeStationaryAction_gap_eq
    {u h k : ℝ} (hh : 0 ≤ h) (hhk : h ≤ k) (hku : k < u) :
    Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) - Real.sqrt (u ^ (2 : ℕ) - k ^ (2 : ℕ)) =
      (k ^ (2 : ℕ) - h ^ (2 : ℕ)) /
        (Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) + Real.sqrt (u ^ (2 : ℕ) - k ^ (2 : ℕ))) := by
  have hrad_h : 0 < u ^ (2 : ℕ) - h ^ (2 : ℕ) := by nlinarith
  have hrad_k : 0 < u ^ (2 : ℕ) - k ^ (2 : ℕ) := by nlinarith
  have hs_h : Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) ^ (2 : ℕ) = u ^ (2 : ℕ) - h ^ (2 : ℕ) :=
    Real.sq_sqrt hrad_h.le
  have hs_k : Real.sqrt (u ^ (2 : ℕ) - k ^ (2 : ℕ)) ^ (2 : ℕ) = u ^ (2 : ℕ) - k ^ (2 : ℕ) :=
    Real.sq_sqrt hrad_k.le
  have hden : Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) + Real.sqrt (u ^ (2 : ℕ) - k ^ (2 : ℕ)) ≠ 0 := by
    positivity
  apply (eq_div_iff hden).mpr
  nlinarith

/-- Deep timelike stationary actions are compressed on every fixed frequency pair. -/
theorem timelikeStationaryAction_gap_le_inverse_height
    {u h k : ℝ} (hh : 0 ≤ h) (hhk : h < k) (hdeep : 2 * k ≤ u) :
    Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) - Real.sqrt (u ^ (2 : ℕ) - k ^ (2 : ℕ)) ≤
      (k ^ (2 : ℕ) - h ^ (2 : ℕ)) / u := by
  have hk0 : 0 < k := lt_of_le_of_lt hh hhk
  have hu0 : 0 < u := lt_of_lt_of_le (by linarith) hdeep
  have hku : k < u := by linarith
  have hrad_order : u ^ (2 : ℕ) - k ^ (2 : ℕ) ≤ u ^ (2 : ℕ) - h ^ (2 : ℕ) := by nlinarith
  have hsqrt_order : Real.sqrt (u ^ (2 : ℕ) - k ^ (2 : ℕ)) ≤
      Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) := Real.sqrt_le_sqrt hrad_order
  have hhalf_sq : (u / 2) ^ (2 : ℕ) ≤ u ^ (2 : ℕ) - k ^ (2 : ℕ) := by nlinarith
  have hhalf_nonneg : 0 ≤ u / 2 := by linarith
  have hsqrt_half : u / 2 ≤ Real.sqrt (u ^ (2 : ℕ) - k ^ (2 : ℕ)) := by
    rw [← Real.sqrt_sq hhalf_nonneg]
    exact Real.sqrt_le_sqrt hhalf_sq
  have hden : u ≤ Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) + Real.sqrt (u ^ (2 : ℕ) - k ^ (2 : ℕ)) := by
    linarith
  have hnum : 0 ≤ k ^ (2 : ℕ) - h ^ (2 : ℕ) := by nlinarith
  rw [timelikeStationaryAction_gap_eq hh hhk.le hku]
  exact div_le_div_of_nonneg_left hnum hu0 hden

/-- A timelike stationary rapidity is confined to an inverse-mass band. -/
theorem timelikeRapidity_le_two_mul_div
    {u h : ℝ} (hh : 0 < h) (hdeep : 2 * h ≤ u) :
    timelikeRapidity u h ≤ 2 * h / u := by
  have hu0 : 0 < u := lt_of_lt_of_le (by linarith) hdeep
  have hhu : h < u := by linarith
  have hsqrt : u / 2 ≤ Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) := by
    have hhalf_sq : (u / 2) ^ (2 : ℕ) ≤ u ^ (2 : ℕ) - h ^ (2 : ℕ) := by nlinarith
    have hhalf_nonneg : 0 ≤ u / 2 := by linarith
    rw [← Real.sqrt_sq hhalf_nonneg]
    exact Real.sqrt_le_sqrt hhalf_sq
  have harg_nonneg : 0 ≤ h / Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) := by positivity
  have harsinh : Real.arsinh (h / Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ))) ≤
      h / Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) := by
    rw [← Real.sinh_le_sinh, Real.sinh_arsinh]
    exact Real.self_le_sinh_iff.mpr harg_nonneg
  rw [timelikeRapidity]
  calc
    Real.arsinh (h / Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ))) ≤
        h / Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)) := harsinh
    _ ≤ h / (u / 2) := div_le_div_of_nonneg_left hh.le (by linarith) hsqrt
    _ = 2 * h / u := by field_simp

/-! ## The spacelike collapse -/

/-- The spacelike rapidity. -/
noncomputable def spacelikeRapidity (u h : ℝ) : ℝ := Real.arsinh (u / Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))

theorem sinh_spacelikeRapidity (u h : ℝ) :
    Real.sinh (spacelikeRapidity u h) = u / Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) := by
  rw [spacelikeRapidity, Real.sinh_arsinh]

theorem cosh_spacelikeRapidity {u h : ℝ} (hu : 0 ≤ u) (hh : 0 < h) (huh : u < h) :
    Real.cosh (spacelikeRapidity u h) = h / Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) := by
  have hr2 : 0 < h ^ (2 : ℕ) - u ^ (2 : ℕ) := by nlinarith
  have hr : 0 < Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) := Real.sqrt_pos.2 hr2
  rw [spacelikeRapidity, Real.cosh_arsinh]
  have hsq : Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) ^ (2 : ℕ) = h ^ (2 : ℕ) - u ^ (2 : ℕ) := Real.sq_sqrt hr2.le
  have hval : 1 + (u / Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ))) ^ (2 : ℕ)
      = (h / Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ))) ^ (2 : ℕ) := by
    field_simp
    nlinarith [hsq]
  rw [hval, Real.sqrt_sq (by positivity)]

/-- **(8.3) The spacelike collapse.**  Outside the light cone the mass phase is a single hyperbolic
sine. -/
theorem massPhase_spacelike {u h : ℝ} (hu : 0 ≤ u) (hh : 0 < h) (huh : u < h) (t : ℝ) :
    u * Real.cosh t + h * Real.sinh t
      = Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) * Real.sinh (t + spacelikeRapidity u h) := by
  have hr2 : 0 < h ^ (2 : ℕ) - u ^ (2 : ℕ) := by nlinarith
  have hr : 0 < Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) := Real.sqrt_pos.2 hr2
  rw [Real.sinh_add, cosh_spacelikeRapidity hu hh huh, sinh_spacelikeRapidity]
  field_simp
  ring

/-- **(8.3) No stationary point.**  Outside the light cone the phase derivative never vanishes. -/
theorem massPhase_spacelike_nonstationary {u h : ℝ} (hu : 0 ≤ u) (hh : 0 < h) (huh : u < h)
    (t : ℝ) : u * Real.sinh t + h * Real.cosh t ≠ 0 := by
  have hr2 : 0 < h ^ (2 : ℕ) - u ^ (2 : ℕ) := by nlinarith
  have hr : 0 < Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) := Real.sqrt_pos.2 hr2
  have hderiv : u * Real.sinh t + h * Real.cosh t
      = Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) * Real.cosh (t + spacelikeRapidity u h) := by
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

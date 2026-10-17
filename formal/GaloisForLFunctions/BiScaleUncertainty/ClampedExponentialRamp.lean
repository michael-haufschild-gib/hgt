import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact polar integration of a continuous one-sided exponential ramp. -/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

/-- A continuous replacement for the cutoff at one, with a right collar of width `ε`. -/
def clampedRamp (ε t : ℝ) : ℝ := min 1 (max 0 ((1+ε-t)/ε))

theorem clampedRamp_nonneg (ε t : ℝ) : 0 ≤ clampedRamp ε t := by
  unfold clampedRamp
  positivity

theorem clampedRamp_le_one (ε t : ℝ) : clampedRamp ε t ≤ 1 := by
  exact min_le_left _ _

theorem continuous_clampedRamp (ε : ℝ) : Continuous (clampedRamp ε) := by
  unfold clampedRamp
  fun_prop

theorem clampedRamp_eq_one {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 1) :
    clampedRamp ε t = 1 := by
  have h : 1 ≤ (1+ε-t)/ε := (le_div_iff₀ hε).2 (by linarith)
  simp [clampedRamp, max_eq_right (by linarith : 0 ≤ (1+ε-t)/ε),
    min_eq_left h]

theorem clampedRamp_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : 1+ε ≤ t) :
    clampedRamp ε t = 0 := by
  have h : (1+ε-t)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  simp [clampedRamp, max_eq_left h]

theorem clampedRamp_eq_linear {ε t : ℝ} (hε : 0 < ε)
    (hlo : 1 ≤ t) (hhi : t ≤ 1+ε) :
    clampedRamp ε t = (1+ε-t)/ε := by
  have h0 : 0 ≤ (1+ε-t)/ε := div_nonneg (by linarith) hε.le
  have h1 : (1+ε-t)/ε ≤ 1 := (div_le_iff₀ hε).2 (by linarith)
  simp [clampedRamp, max_eq_right h0, min_eq_right h1]

theorem antitone_clampedRamp {ε : ℝ} (hε : 0 < ε) : Antitone (clampedRamp ε) := by
  intro a b hab
  unfold clampedRamp
  gcongr

/-- The logarithmic polar contribution of the collar. -/
def rampLogCorrection (ε : ℝ) : ℝ := ((1+ε)*Real.log (1+ε)-ε)/ε

end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

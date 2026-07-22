import GaloisForLFunctions.RHTower.SoninApertureRestrictionDefect
import GaloisForLFunctions.RHTower.SoninPrincipalShellCyclicTrace

/-!
# Conservation of principal cyclic mass under Sonin aperture restriction

A strict aperture enlargement does create a noncompact positive restriction defect.  The exact
principal normal form, however, reveals a stronger law: the enlarged-aperture diagonal shell is
the algebraic sum of the retained old shell and the lost-aperture shell.  The canonical cyclic
logarithmic reader is additive on this split.  Its lost mass is the aperture cocycle
`log b - log a`, while retained plus lost mass is exactly the original orbital mass `log r`.

Thus aperture restriction is not an anomaly of the enlarged principal algebra.  It conserves
source mass by transferring a path-independent logarithmic coboundary between two noncompact
principal channels.
-/

noncomputable section

namespace RHTower

/-- Canonical scale-one normal window for a two-polarization shell above aperture `a`. -/
def soninScaleOneShellWindow
    (a s t : ℝ) (has : a ≤ s) (hst : s < t) : SoninLiveWindow a where
  ceiling := t
  floor := s
  scale := 1
  scale_pos := zero_lt_one
  base_le_floor := has
  floor_lt_ceiling := hst
  domain_le := by simpa using has

/-- A canonical scale-one window represents its two-polarization shell exactly, not only modulo
compact or relative operators. -/
theorem soninScaleOneShellWindow_operator
    (a s t : ℝ) (has : a ≤ s) (hst : s < t) :
    (soninScaleOneShellWindow a s t has hst).operator =
      evenTwoPolarizationShell s t := by
  dsimp only [soninScaleOneShellWindow, SoninLiveWindow.operator,
    SoninWindowState.operator, evenSoninWindowTranslation,
    evenPhysicalWindowTranslation, evenFourierWindowTranslation,
    evenTwoPolarizationShell]
  rw [evenDilationCLM_one]
  simp only [inv_one, evenDilationCLM_one, mul_one]
  have hp := evenIndicatorCutoff_shellComplementProduct t s a
    (has.trans hst.le)
  have hf := evenFourierCutoff_shellComplementProduct t s a
    (has.trans hst.le)
  rw [hp, hf, max_eq_left has]

/-- The canonical cyclic mass of a scale-one shell is its logarithmic width. -/
theorem soninLiveWindowCyclicLogWeight_scaleOneShell
    (a s t : ℝ) (has : a ≤ s) (hst : s < t) :
    soninLiveWindowCyclicLogWeight (soninScaleOneShellWindow a s t has hst) =
      Real.log t - Real.log s := by
  simp [soninLiveWindowCyclicLogWeight, soninScaleOneShellWindow]

/-- Part of the old prime shell retained after restriction from aperture `a` to `b`. -/
def soninApertureRetainedLayerWindow
    (a b r : ℝ) (_hab : a < b) (_hr : 1 < r)
    (hbr : b < r * a) : SoninLiveWindow b :=
  soninScaleOneShellWindow b b (r * a) le_rfl hbr

/-- Noncompact shell lost when the aperture grows from `a` to `b`. -/
def soninApertureCyclicLostLayerWindow
    (a b r : ℝ) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) : SoninLiveWindow b :=
  soninScaleOneShellWindow b (r * a) (r * b) hbr.le
    (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr))

/-- Full diagonal prime shell at the enlarged aperture. -/
def soninApertureTotalLayerWindow
    (a b r : ℝ) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) : SoninLiveWindow b :=
  soninScaleOneShellWindow b b (r * b) le_rfl
    (lt_trans hbr (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr)))

theorem soninApertureRetainedLayerWindow_operator
    (a b r : ℝ) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    (soninApertureRetainedLayerWindow a b r hab hr hbr).operator =
      evenTwoPolarizationShell b (r * a) := by
  exact soninScaleOneShellWindow_operator b b (r * a) le_rfl hbr

theorem soninApertureTotalLayerWindow_operator
    (a b r : ℝ) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    (soninApertureTotalLayerWindow a b r hab hr hbr).operator =
      evenTwoPolarizationShell b (r * b) := by
  exact soninScaleOneShellWindow_operator b b (r * b) le_rfl
    (lt_trans hbr (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr)))

theorem soninApertureCyclicLostLayerWindow_operator
    (a b r : ℝ) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    (soninApertureCyclicLostLayerWindow a b r hab hr hbr).operator =
      evenTwoPolarizationShell (r * a) (r * b) := by
  exact soninScaleOneShellWindow_operator b (r * a) (r * b) hbr.le
    (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr))

/-- **Exact operator conservation.** The enlarged-aperture prime shell is the algebraic sum of
the retained old shell and the noncompact lost-aperture shell. -/
theorem soninApertureTotalLayerWindow_operator_eq_retained_add_lost
    (a b r : ℝ) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    (soninApertureTotalLayerWindow a b r hab hr hbr).operator =
      (soninApertureRetainedLayerWindow a b r hab hr hbr).operator +
        (soninApertureCyclicLostLayerWindow a b r hab hr hbr).operator := by
  rw [soninApertureTotalLayerWindow_operator,
    soninApertureRetainedLayerWindow_operator,
    soninApertureCyclicLostLayerWindow_operator]
  unfold evenTwoPolarizationShell
  abel

theorem soninLiveWindowCyclicLogWeight_apertureRetainedLayer
    (a b r : ℝ) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    soninLiveWindowCyclicLogWeight
        (soninApertureRetainedLayerWindow a b r hab hr hbr) =
      Real.log (r * a) - Real.log b := by
  exact soninLiveWindowCyclicLogWeight_scaleOneShell b b (r * a) le_rfl hbr

theorem soninLiveWindowCyclicLogWeight_apertureTotalLayer
    (a b r : ℝ) (hb : 0 < b) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    soninLiveWindowCyclicLogWeight
        (soninApertureTotalLayerWindow a b r hab hr hbr) = Real.log r := by
  unfold soninApertureTotalLayerWindow
  rw [soninLiveWindowCyclicLogWeight_scaleOneShell]
  rw [Real.log_mul (zero_lt_one.trans hr).ne' hb.ne']
  ring

/-- The noncompact lost channel carries exactly the aperture cocycle, independently of the prime
or dilation scale crossing the annulus. -/
theorem soninLiveWindowCyclicLogWeight_apertureCyclicLostLayer
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    soninLiveWindowCyclicLogWeight
        (soninApertureCyclicLostLayerWindow a b r hab hr hbr) =
      Real.log b - Real.log a := by
  have hb : 0 < b := ha.trans hab
  unfold soninApertureCyclicLostLayerWindow
  rw [soninLiveWindowCyclicLogWeight_scaleOneShell]
  rw [Real.log_mul (zero_lt_one.trans hr).ne' hb.ne',
    Real.log_mul (zero_lt_one.trans hr).ne' ha.ne']
  ring

/-- **Aperture cyclic-mass conservation.** Restriction splits a diagonal orbital mass into a
retained principal shell and a noncompact lost shell, but their canonical cyclic masses add
exactly to the original `log r`, independently of both apertures. -/
theorem soninAperture_cyclicMass_conservation
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    soninLiveWindowCyclicLogWeight
          (soninApertureRetainedLayerWindow a b r hab hr hbr) +
        soninLiveWindowCyclicLogWeight
          (soninApertureCyclicLostLayerWindow a b r hab hr hbr) =
      Real.log r := by
  rw [soninLiveWindowCyclicLogWeight_apertureRetainedLayer,
    soninLiveWindowCyclicLogWeight_apertureCyclicLostLayer a b r ha hab hr hbr]
  rw [Real.log_mul (zero_lt_one.trans hr).ne' ha.ne']
  ring

/-- The lost aperture mass is an exact additive one-cocycle on every nested triple. -/
theorem soninAperture_cyclicMass_cocycle
    (a b c : ℝ) :
    (Real.log c - Real.log a) =
      (Real.log b - Real.log a) + (Real.log c - Real.log b) := by
  ring

end RHTower

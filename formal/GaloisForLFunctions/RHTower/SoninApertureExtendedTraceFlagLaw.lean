import GaloisForLFunctions.RHTower.SoninApertureCurvatureTrace
import GaloisForLFunctions.RHTower.SoninApertureCyclicMassConservation
import GaloisForLFunctions.RHTower.SoninPrincipalRelativeCyclicExtension

/-!
# One-sided aperture flag law for the extended Sonin trace

The strict aperture restriction defect is a principal-relative operator: its noncompact part is the
canonical scale-one lost shell and its remainder is Schatten-1.  Because the base aperture of the
enclosing chamber lies below the lost floor, all three defects of a strict flag `a < b < c < r*a`
are presented at the single base aperture `c`, so one extended trace reads them all.

On that common presentation the logarithmic principal weight is an exact coboundary and cancels,
so the entire failure of additivity along the flag is the ordinary trace of the aperture curvature.
That trace was already identified with minus a Hilbert--Schmidt energy, so the extended trace is
subadditive along strict aperture flags with an exactly computed, definitely signed defect.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open SoninPrincipalRelativeOperator

/-- The strict aperture restriction defect presented at a base aperture `e` below the lost floor:
canonical scale-one lost shell plus an exact relative correction. -/
def soninApertureRestrictionDefectPresentation
    (e a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) (hea : e ≤ r * a) :
    SoninPrincipalRelativeOperator e where
  state := SoninWindowState.live
    (soninScaleOneShellWindow e (r * a) (r * b) hea
      (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr)))
  relative := evenSoninApertureRestrictionDefect a b r hr -
    evenTwoPolarizationShell (r * a) (r * b)
  relative_mem :=
    evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell
      ha hab hr hbr

@[simp] theorem toOperator_soninApertureRestrictionDefectPresentation
    (e a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) (hea : e ≤ r * a) :
    toOperator (soninApertureRestrictionDefectPresentation e a b r ha hab hr hbr hea) =
      evenSoninApertureRestrictionDefect a b r hr := by
  have hshell := soninScaleOneShellWindow_operator e (r * a) (r * b) hea
    (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr))
  simp only [toOperator, soninApertureRestrictionDefectPresentation]
  rw [show (SoninWindowState.live
      (soninScaleOneShellWindow e (r * a) (r * b) hea
        (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr)))).operator =
        evenTwoPolarizationShell (r * a) (r * b) from hshell]
  abel

/-- **Exact aperture-defect value.**  The extended trace of one strict aperture defect is the
additive aperture cocycle plus the ordinary trace of its Schatten-1 shell residual. -/
theorem extendedTrace_soninApertureRestrictionDefectPresentation
    (e a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) (hea : e ≤ r * a) :
    extendedTrace (soninApertureRestrictionDefectPresentation e a b r ha hab hr hbr hea) =
      ((Real.log b - Real.log a : ℝ) : ℂ) +
        opTrace (evenSoninApertureRestrictionDefect a b r hr -
          evenTwoPolarizationShell (r * a) (r * b)) := by
  have hb : 0 < b := ha.trans hab
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hweight := soninLiveWindowCyclicLogWeight_scaleOneShell e (r * a) (r * b) hea
    (mul_lt_mul_of_pos_left hab hr0)
  have hlog : Real.log (r * b) - Real.log (r * a) = Real.log b - Real.log a := by
    rw [Real.log_mul hr0.ne' hb.ne', Real.log_mul hr0.ne' ha.ne']
    ring
  unfold extendedTrace soninApertureRestrictionDefectPresentation
  simp only
  rw [show soninWindowStateCyclicLogTrace
      (SoninWindowState.live
        (soninScaleOneShellWindow e (r * a) (r * b) hea
          (mul_lt_mul_of_pos_left hab hr0))) =
        Real.log (r * b) - Real.log (r * a) from hweight, hlog]

/-- Shell residuals of a strict aperture flag differ exactly by the aperture curvature: the
two-polarization shells telescope, so no principal term survives. -/
theorem soninApertureShellResidual_flag
    {a b c r : ℝ} (hr : 1 < r) :
    evenSoninApertureRestrictionDefect a c r hr -
        evenTwoPolarizationShell (r * a) (r * c) =
      (evenSoninApertureRestrictionDefect a b r hr -
          evenTwoPolarizationShell (r * a) (r * b)) +
        (evenSoninApertureRestrictionDefect b c r hr -
            evenTwoPolarizationShell (r * b) (r * c)) +
          evenSoninApertureRestrictionCurvature a b c r hr := by
  unfold evenSoninApertureRestrictionCurvature evenTwoPolarizationShell
  abel

/-- The ordinary traces of the three shell residuals of a strict aperture flag differ exactly by
the trace of the aperture curvature. -/
theorem opTrace_soninApertureShellResidual_flag
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    opTrace (evenSoninApertureRestrictionDefect a c r hr -
        evenTwoPolarizationShell (r * a) (r * c)) =
      opTrace (evenSoninApertureRestrictionDefect a b r hr -
          evenTwoPolarizationShell (r * a) (r * b)) +
        opTrace (evenSoninApertureRestrictionDefect b c r hr -
            evenTwoPolarizationShell (r * b) (r * c)) +
          opTrace (evenSoninApertureRestrictionCurvature a b c r hr) := by
  have hb : 0 < b := ha.trans hab
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hbra : b < r * a := hbc.trans hcr
  have hcrb : c < r * b := hcr.trans (mul_lt_mul_of_pos_left hab hr0)
  have hab' := evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell
    ha hab hr hbra
  have hbc' := evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell
    hb hbc hr hcrb
  have hK := evenSoninApertureRestrictionCurvature_mem_principalRelativeIdeal
    ha hab hbc hr hcr
  have hab'' : IsSoninPrincipalRelativeIdeal
      (evenSoninApertureRestrictionDefect a b r hr -
        evenTwoPolarizationShell (r * a) (r * b)) := hab'
  have hbc'' : IsSoninPrincipalRelativeIdeal
      (evenSoninApertureRestrictionDefect b c r hr -
        evenTwoPolarizationShell (r * b) (r * c)) := hbc'
  rw [soninApertureShellResidual_flag (a := a) (b := b) (c := c) hr,
    opTrace_add_of_memSchattenClass_one
      (hab''.add hbc'').memSchattenClass_one hK.memSchattenClass_one,
    opTrace_add_of_memSchattenClass_one
      hab''.memSchattenClass_one hbc''.memSchattenClass_one]

/-- **Extended-trace aperture flag law.**  Read at the single base aperture `c`, the extended trace
of the total aperture defect is the sum of the two successive extended traces plus the ordinary
trace of the aperture curvature.  The logarithmic principal weights cancel exactly. -/
theorem extendedTrace_soninApertureRestrictionDefect_flag
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    extendedTrace (soninApertureRestrictionDefectPresentation c a c r ha
        (hab.trans hbc) hr hcr hcr.le) =
      extendedTrace (soninApertureRestrictionDefectPresentation c a b r ha hab hr
          (hbc.trans hcr) hcr.le) +
        extendedTrace (soninApertureRestrictionDefectPresentation c b c r
            (ha.trans hab) hbc hr
            (hcr.trans (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr)))
            (hcr.le.trans
              (mul_le_mul_of_nonneg_left hab.le (zero_lt_one.trans hr).le))) +
          opTrace (evenSoninApertureRestrictionCurvature a b c r hr) := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  rw [extendedTrace_soninApertureRestrictionDefectPresentation,
    extendedTrace_soninApertureRestrictionDefectPresentation,
    extendedTrace_soninApertureRestrictionDefectPresentation,
    opTrace_soninApertureShellResidual_flag ha hab hbc hr hcr]
  have hlog : ((Real.log c - Real.log a : ℝ) : ℂ) =
      ((Real.log b - Real.log a : ℝ) : ℂ) + ((Real.log c - Real.log b : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hlog]
  ring

/-- **Exact scalar flag defect.**  The real extended trace loses exactly the coupling energy
between the two successive lost aperture layers. -/
theorem re_extendedTrace_soninApertureRestrictionDefect_flag
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    (extendedTrace (soninApertureRestrictionDefectPresentation c a c r ha
        (hab.trans hbc) hr hcr hcr.le)).re =
      (extendedTrace (soninApertureRestrictionDefectPresentation c a b r ha hab hr
          (hbc.trans hcr) hcr.le)).re +
        (extendedTrace (soninApertureRestrictionDefectPresentation c b c r
            (ha.trans hab) hbc hr
            (hcr.trans (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr)))
            (hcr.le.trans
              (mul_le_mul_of_nonneg_left hab.le (zero_lt_one.trans hr).le)))).re -
          hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  rw [extendedTrace_soninApertureRestrictionDefect_flag ha hab hbc hr hcr]
  simp only [Complex.add_re]
  rw [re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
    ha hab hbc hr hcr]
  ring

/-- **One-sided aperture flag law.**  The extended trace is subadditive along every strict
aperture flag: enlarging in one step never reads more than enlarging in two. -/
theorem re_extendedTrace_soninApertureRestrictionDefect_flag_le
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    (extendedTrace (soninApertureRestrictionDefectPresentation c a c r ha
        (hab.trans hbc) hr hcr hcr.le)).re ≤
      (extendedTrace (soninApertureRestrictionDefectPresentation c a b r ha hab hr
          (hbc.trans hcr) hcr.le)).re +
        (extendedTrace (soninApertureRestrictionDefectPresentation c b c r
            (ha.trans hab) hbc hr
            (hcr.trans (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr)))
            (hcr.le.trans
              (mul_le_mul_of_nonneg_left hab.le (zero_lt_one.trans hr).le)))).re := by
  rw [re_extendedTrace_soninApertureRestrictionDefect_flag ha hab hbc hr hcr]
  have hnn := hsNormSq_nonneg
    (evenSoninApertureSuccessiveLayerTransition a b c r hr)
  linarith

/-- Equality in the flag law happens exactly when the two successive lost layers do not couple. -/
theorem re_extendedTrace_soninApertureRestrictionDefect_flag_eq_iff
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    (extendedTrace (soninApertureRestrictionDefectPresentation c a c r ha
        (hab.trans hbc) hr hcr hcr.le)).re =
      (extendedTrace (soninApertureRestrictionDefectPresentation c a b r ha hab hr
          (hbc.trans hcr) hcr.le)).re +
        (extendedTrace (soninApertureRestrictionDefectPresentation c b c r
            (ha.trans hab) hbc hr
            (hcr.trans (mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr)))
            (hcr.le.trans
              (mul_le_mul_of_nonneg_left hab.le (zero_lt_one.trans hr).le)))).re ↔
      evenSoninApertureRestrictionCurvature a b c r hr = 0 := by
  have hZ := evenSoninApertureSuccessiveLayerTransition_isHilbertSchmidt
    ha hab hbc hr hcr
  have hflag := re_extendedTrace_soninApertureRestrictionDefect_flag
    ha hab hbc hr hcr
  have hrigid :=
    evenSoninApertureRestrictionCurvature_eq_zero_iff_successiveLayerTransition_eq_zero
      ha hab hbc hr hcr
  constructor
  · intro heq
    rw [hflag] at heq
    have hzero : hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) = 0 := by
      linarith
    exact hrigid.mpr ((hsNormSq_eq_zero_iff hZ).mp hzero)
  · intro hzero
    have hnorm : hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) = 0 :=
      (hsNormSq_eq_zero_iff hZ).mpr (hrigid.mp hzero)
    rw [hflag, hnorm]
    ring

end RHTower

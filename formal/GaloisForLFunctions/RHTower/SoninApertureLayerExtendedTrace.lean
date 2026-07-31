import GaloisForLFunctions.RHTower.SoninShellProductIdeal
import GaloisForLFunctions.RHTower.SoninApertureExtendedTraceFlagLaw

/-!
# The aperture layer read by the extended trace

The layer–shell congruence makes the aperture layer itself a principal-relative operator: its
principal part is the scale-one shell between the two apertures, and its remainder is Schatten-1.

The extended trace therefore reads the layer directly, and its principal value is the aperture
cocycle.  Previously only the aperture *defect* had such a reading; the layer is the more primitive
object, and it carries the same cocycle.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open SoninPrincipalRelativeOperator

/-- The aperture layer presented as a principal-relative operator: scale-one shell plus a
Schatten-1 remainder. -/
def soninApertureLayerPresentation (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    SoninPrincipalRelativeOperator a where
  state := SoninWindowState.live (soninScaleOneShellWindow a a b le_rfl hab)
  relative := evenSoninApertureLayer a b - evenTwoPolarizationShell a b
  relative_mem :=
    evenSoninApertureLayer_principalRelativeEq_twoPolarizationShell ha
      (ha.trans hab) hab.le

@[simp] theorem toOperator_soninApertureLayerPresentation
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    toOperator (soninApertureLayerPresentation a b ha hab) =
      evenSoninApertureLayer a b := by
  have hshell := soninScaleOneShellWindow_operator a a b le_rfl hab
  simp only [toOperator, soninApertureLayerPresentation]
  rw [show (SoninWindowState.live (soninScaleOneShellWindow a a b le_rfl hab)).operator =
      evenTwoPolarizationShell a b from hshell]
  abel

/-- **Extended trace of the aperture layer.**  Its principal value is the aperture cocycle, and the
rest is the ordinary trace of a Schatten-1 remainder. -/
theorem extendedTrace_soninApertureLayerPresentation
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    extendedTrace (soninApertureLayerPresentation a b ha hab) =
      ((Real.log b - Real.log a : ℝ) : ℂ) +
        opTrace (evenSoninApertureLayer a b - evenTwoPolarizationShell a b) := by
  have hweight := soninLiveWindowCyclicLogWeight_scaleOneShell a a b le_rfl hab
  unfold extendedTrace soninApertureLayerPresentation
  simp only
  rw [show soninWindowStateCyclicLogTrace
      (SoninWindowState.live (soninScaleOneShellWindow a a b le_rfl hab)) =
        Real.log b - Real.log a from hweight]

/-- The layer and the defect carry the same principal cocycle: the aperture layer between `a` and
`b`, and the aperture defect between them at any crossing scale, both read `log b - log a`. -/
theorem extendedTrace_soninApertureLayerPresentation_principal_eq_defect_principal
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    extendedTrace (soninApertureLayerPresentation a b ha hab) -
        opTrace (evenSoninApertureLayer a b - evenTwoPolarizationShell a b) =
      ((Real.log b - Real.log a : ℝ) : ℂ) := by
  rw [extendedTrace_soninApertureLayerPresentation a b ha hab]
  ring

end RHTower

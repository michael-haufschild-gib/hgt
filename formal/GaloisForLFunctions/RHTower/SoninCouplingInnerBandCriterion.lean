import GaloisForLFunctions.RHTower.SoninApertureDefectSupport
import GaloisForLFunctions.RHTower.SoninInnerBandAnnihilation

/-!
# The coupling agrees with the lost transition on the inner band

On a vector supported inside the outer window the projection at `c` vanishes exactly, so the
successive-layer coupling and the lost-layer transition act identically there.

This turns the search for a nonzero coupling into a question about the lost transition, which is
the operator the corpus already knows to be noncompact: the coupling is nonzero as soon as the lost
transition fails to annihilate the inner band.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- On an inner-band vector the coupling is the lost transition. -/
theorem evenSoninApertureSuccessiveLayerTransition_apply_of_indicatorCutoff_eq_self
    {a b c r : ℝ} (hbc : b ≤ c) (hr : 1 < r) {w : evenSubspace}
    (hw : evenIndicatorCutoff c w = w) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr w =
      evenSoninApertureLostTransition a b r hr w := by
  rw [evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc hr]
  have hQ : evenCentralSoninProjection c w = 0 :=
    evenCentralSoninProjection_eq_zero_of_indicatorCutoff_eq_self c hw
  change evenSoninApertureLostTransition a b r hr
    ((1 - evenCentralSoninProjection c) w) = _
  rw [sub_apply, one_apply_eq_self, hQ, sub_zero]

/-- The same for a vector band-limited to the outer window. -/
theorem evenSoninApertureSuccessiveLayerTransition_apply_of_fourierCutoff_eq_self
    {a b c r : ℝ} (hbc : b ≤ c) (hr : 1 < r) {w : evenSubspace}
    (hw : evenFourierCutoff c w = w) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr w =
      evenSoninApertureLostTransition a b r hr w := by
  rw [evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc hr]
  have hQ : evenCentralSoninProjection c w = 0 :=
    evenCentralSoninProjection_eq_zero_of_fourierCutoff_eq_self c hw
  change evenSoninApertureLostTransition a b r hr
    ((1 - evenCentralSoninProjection c) w) = _
  rw [sub_apply, one_apply_eq_self, hQ, sub_zero]

/-- **Inner-band witness criterion.**  The coupling is nonzero as soon as the lost transition fails
to annihilate some vector supported inside the outer window.  This reduces the witness search from
the coupling, whose range is hard to describe, to the lost transition, whose noncompactness the
corpus already proves. -/
theorem evenSoninApertureSuccessiveLayerTransition_ne_zero_of_lostTransition_apply_ne_zero
    {a b c r : ℝ} (hbc : b ≤ c) (hr : 1 < r) {w : evenSubspace}
    (hw : evenIndicatorCutoff c w = w)
    (hne : evenSoninApertureLostTransition a b r hr w ≠ 0) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr ≠ 0 := by
  intro hzero
  apply hne
  rw [← evenSoninApertureSuccessiveLayerTransition_apply_of_indicatorCutoff_eq_self
    (a := a) hbc hr hw, hzero]
  rfl

/-- Contrapositive: a vanishing coupling forces the lost transition to annihilate the whole inner
band. -/
theorem evenSoninApertureLostTransition_apply_eq_zero_of_coupling_eq_zero
    {a b c r : ℝ} (hbc : b ≤ c) (hr : 1 < r)
    (hzero : evenSoninApertureSuccessiveLayerTransition a b c r hr = 0)
    {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    evenSoninApertureLostTransition a b r hr w = 0 := by
  rw [← evenSoninApertureSuccessiveLayerTransition_apply_of_indicatorCutoff_eq_self
    (a := a) hbc hr hw, hzero]
  rfl

end RHTower

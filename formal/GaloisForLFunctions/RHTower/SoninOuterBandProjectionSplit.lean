import GaloisForLFunctions.RHTower.SoninCouplingInnerBandCriterion

/-!
# Sonin projection of a vector outside the physical window

On a vector annihilated by the physical cutoff the Sonin projection splits exactly into a
band-pass part and a trace-class correction: the formal complement `1 - A_b - R_b` loses its
physical term, leaving `1 - R_b`, and the exact projection correction supplies the rest.

This is the reduction the coupling question needs.  The obstruction to evaluating the lost
transition on an annulus vector was that the Sonin projection spreads its support with no upper
bound; the split isolates that spreading into the single classical operator `1 - R_b`, with
everything else trace class.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **Outer-band split of the Sonin projection.**  On a vector killed by the physical cutoff the
Sonin projection is the Fourier band-pass plus the exact projection correction. -/
theorem evenCentralSoninProjection_apply_of_indicatorCutoff_eq_zero
    (b : ℝ) {w : evenSubspace} (hw : evenIndicatorCutoff b w = 0) :
    evenCentralSoninProjection b w =
      (w - evenFourierCutoff b w) + evenSoninProjectionCorrection b w := by
  have h : evenSoninProjectionCorrection b w =
      evenCentralSoninProjection b w -
        (w - evenIndicatorCutoff b w - evenFourierCutoff b w) := by
    change (evenCentralSoninProjection b -
      (1 - evenIndicatorCutoff b - evenFourierCutoff b)) w = _
    simp only [sub_apply, one_apply_eq_self]
  rw [hw, sub_zero] at h
  rw [h]
  abel

/-- The lost-layer transition on an outer-band vector, with the Sonin projection resolved into its
band-pass part and a trace-class correction. -/
theorem evenSoninApertureLostTransition_apply_of_indicatorCutoff_eq_zero
    (a b r : ℝ) (hr : 1 < r) {w : evenSubspace}
    (hw : evenIndicatorCutoff b w = 0) :
    evenSoninApertureLostTransition a b r hr w =
      evenSoninApertureLayer a b (evenDilationSum r hr
        ((w - evenFourierCutoff b w) + evenSoninProjectionCorrection b w)) := by
  unfold evenSoninApertureLostTransition
  change evenSoninApertureLayer a b (evenDilationSum r hr
    (evenCentralSoninProjection b w)) = _
  rw [evenCentralSoninProjection_apply_of_indicatorCutoff_eq_zero b hw]

/-- **Reduced form of the coupling on the inner band.**  For a vector living in the annulus between
the two apertures — killed by the physical cutoff at `b` and fixed by the one at `c` — the
successive-layer coupling is the aperture layer applied to the dilated band-pass of the vector, up
to the exact trace-class correction. -/
theorem evenSoninApertureSuccessiveLayerTransition_apply_annulus
    {a b c r : ℝ} (hbc : b ≤ c) (hr : 1 < r) {w : evenSubspace}
    (hlow : evenIndicatorCutoff b w = 0) (hhigh : evenIndicatorCutoff c w = w) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr w =
      evenSoninApertureLayer a b (evenDilationSum r hr
        ((w - evenFourierCutoff b w) + evenSoninProjectionCorrection b w)) := by
  rw [evenSoninApertureSuccessiveLayerTransition_apply_of_indicatorCutoff_eq_self
    (a := a) hbc hr hhigh,
    evenSoninApertureLostTransition_apply_of_indicatorCutoff_eq_zero a b r hr hlow]

/-- The correction appearing in the split is Schatten-1, so the whole obstruction sits in the
band-pass term. -/
theorem memSchattenClass_one_evenSoninProjectionCorrection
    {b : ℝ} (hb : 0 < b) :
    MemSchattenClass 1 (evenSoninProjectionCorrection b) :=
  IsSoninPrincipalRelativeIdeal.projectionCorrection_memSchattenClass_one b hb

end RHTower

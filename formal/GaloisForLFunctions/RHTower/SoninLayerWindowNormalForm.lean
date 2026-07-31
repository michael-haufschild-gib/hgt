import GaloisForLFunctions.RHTower.SoninCouplingOuterCompression

/-!
# The aperture layer is the outer window on the inner carrier, modulo trace class

The complement of a Sonin projection is the sum of its two forbidden cutoffs up to the exact
projection correction.  Feeding that into the left absorption of the aperture layer, and using that
each cutoff annihilates its own projection, expresses the layer through the elementary cutoffs:

it is the outer window, in both polarizations, restricted to the inner carrier — plus a Schatten-1
error.

This replaces the layer, whose range is defined by an orthogonality condition, with explicit
cutoffs.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The complement of a Sonin projection is its two forbidden cutoffs, up to the exact
correction. -/
theorem one_sub_evenCentralSoninProjection_eq
    (c : ℝ) :
    1 - evenCentralSoninProjection c =
      evenIndicatorCutoff c + evenFourierCutoff c -
        evenSoninProjectionCorrection c := by
  unfold evenSoninProjectionCorrection
  abel

/-- **Window normal form of the aperture layer.**  The layer is the outer window on the inner
carrier, corrected by a Schatten-1 term. -/
theorem evenSoninApertureLayer_eq_window_sub_correction
    {b c : ℝ} (hbc : b ≤ c) :
    evenSoninApertureLayer b c =
      (evenIndicatorCutoff c + evenFourierCutoff c) *
          evenCentralSoninProjection b -
        evenSoninProjectionCorrection c * evenSoninApertureLayer b c := by
  have habs := one_sub_evenCentralSoninProjection_mul_evenSoninApertureLayer hbc
  have hA : evenIndicatorCutoff c * evenSoninApertureLayer b c =
      evenIndicatorCutoff c * evenCentralSoninProjection b := by
    unfold evenSoninApertureLayer
    rw [mul_sub, evenIndicatorCutoff_mul_evenCentralSoninProjection, sub_zero]
  have hR : evenFourierCutoff c * evenSoninApertureLayer b c =
      evenFourierCutoff c * evenCentralSoninProjection b := by
    unfold evenSoninApertureLayer
    rw [mul_sub, evenFourierCutoff_mul_evenCentralSoninProjection, sub_zero]
  calc
    evenSoninApertureLayer b c
        = (1 - evenCentralSoninProjection c) * evenSoninApertureLayer b c :=
      habs.symm
    _ = (evenIndicatorCutoff c + evenFourierCutoff c -
          evenSoninProjectionCorrection c) * evenSoninApertureLayer b c := by
      rw [one_sub_evenCentralSoninProjection_eq c]
    _ = evenIndicatorCutoff c * evenSoninApertureLayer b c +
          evenFourierCutoff c * evenSoninApertureLayer b c -
            evenSoninProjectionCorrection c * evenSoninApertureLayer b c := by
      rw [sub_mul, add_mul]
    _ = (evenIndicatorCutoff c + evenFourierCutoff c) *
          evenCentralSoninProjection b -
            evenSoninProjectionCorrection c * evenSoninApertureLayer b c := by
      rw [hA, hR, add_mul]

/-- The correction term of the window normal form lies in the concrete relative ideal. -/
theorem isSoninPrincipalRelativeIdeal_layerWindowCorrection
    {b c : ℝ} (hc : 0 < c) :
    IsSoninPrincipalRelativeIdeal
      (evenSoninProjectionCorrection c * evenSoninApertureLayer b c) :=
  (IsSoninPrincipalRelativeIdeal.projectionCorrection c hc).rightMul _

/-- Hence the layer agrees with the outer window on the inner carrier modulo the exact relative
ideal. -/
theorem evenSoninApertureLayer_principalRelativeEq_window
    {b c : ℝ} (hbc : b ≤ c) (hc : 0 < c) :
    evenSoninApertureLayer b c =ᵣ
      (evenIndicatorCutoff c + evenFourierCutoff c) *
        evenCentralSoninProjection b := by
  have heq := evenSoninApertureLayer_eq_window_sub_correction hbc
  unfold SoninPrincipalRelativeEq
  have hadd : evenSoninApertureLayer b c +
      evenSoninProjectionCorrection c * evenSoninApertureLayer b c =
      (evenIndicatorCutoff c + evenFourierCutoff c) *
        evenCentralSoninProjection b := eq_sub_iff_add_eq.mp heq
  have hdiff : evenSoninApertureLayer b c -
      (evenIndicatorCutoff c + evenFourierCutoff c) *
        evenCentralSoninProjection b =
      -(evenSoninProjectionCorrection c * evenSoninApertureLayer b c) := by
    rw [← hadd]
    abel
  rw [hdiff]
  exact (isSoninPrincipalRelativeIdeal_layerWindowCorrection (b := b) hc).neg

end RHTower

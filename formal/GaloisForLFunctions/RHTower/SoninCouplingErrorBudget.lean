import GaloisForLFunctions.RHTower.SoninCouplingDilateDistance
import GaloisForLFunctions.RHTower.SoninIdealBadModeCount
import GaloisForLFunctions.RHTower.SoninDilatedPacketLayerLimit

/-!
# The coupling's full error budget against the dilate

Expanding the aperture layer into its shell, band and correction parts turns the distance from the
coupling's image to the dilate into five terms: two projection corrections, the physical shell on
the dilate, two band terms for the dilate, and the vector's own band content.

Each term is controlled by a different mechanism — the shell vanishes on support, the corrections
are relative-ideal errors and so spoil only boundedly many modes, and the band terms are measured by
the spectral estimates.  Writing the corrections as ideal operators applied to the vector itself,
rather than to its dilate, is what lets the mode count see them: the ideal absorbs the dilation by
right multiplication.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **The layer defect splits.**  Physical shell, two band terms, and a correction difference. -/
theorem norm_evenSoninApertureLayer_sub_le (a b : ℝ) (v : evenSubspace) :
    ‖evenSoninApertureLayer a b v - v‖ ≤
      ‖(evenIndicatorCutoff b - evenIndicatorCutoff a) v‖ +
        (‖v - evenFourierCutoff b v‖ + ‖evenFourierCutoff a v‖) +
        ‖(evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) v‖ := by
  have hdecomp : evenSoninApertureLayer a b v - v =
      (evenIndicatorCutoff b - evenIndicatorCutoff a) v +
        ((evenFourierCutoff b - evenFourierCutoff a) v - v) +
        (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) v := by
    rw [evenSoninApertureLayer_eq_shell_add_correctionDiff a b]
    simp only [add_apply]
    abel
  have hband : ‖(evenFourierCutoff b - evenFourierCutoff a) v - v‖ ≤
      ‖v - evenFourierCutoff b v‖ + ‖evenFourierCutoff a v‖ := by
    have hsplit : (evenFourierCutoff b - evenFourierCutoff a) v - v =
        -(v - evenFourierCutoff b v) - evenFourierCutoff a v := by
      rw [sub_apply]
      abel
    rw [hsplit]
    calc ‖-(v - evenFourierCutoff b v) - evenFourierCutoff a v‖
        ≤ ‖-(v - evenFourierCutoff b v)‖ + ‖evenFourierCutoff a v‖ := norm_sub_le _ _
      _ = ‖v - evenFourierCutoff b v‖ + ‖evenFourierCutoff a v‖ := by rw [norm_neg]
  rw [hdecomp]
  calc ‖(evenIndicatorCutoff b - evenIndicatorCutoff a) v +
          ((evenFourierCutoff b - evenFourierCutoff a) v - v) +
          (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) v‖
      ≤ ‖(evenIndicatorCutoff b - evenIndicatorCutoff a) v +
            ((evenFourierCutoff b - evenFourierCutoff a) v - v)‖ +
          ‖(evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) v‖ :=
        norm_add_le _ _
    _ ≤ (‖(evenIndicatorCutoff b - evenIndicatorCutoff a) v‖ +
            ‖(evenFourierCutoff b - evenFourierCutoff a) v - v‖) +
          ‖(evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) v‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖(evenIndicatorCutoff b - evenIndicatorCutoff a) v‖ +
          (‖v - evenFourierCutoff b v‖ + ‖evenFourierCutoff a v‖) +
          ‖(evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) v‖ := by
        gcongr

/-- The correction difference precomposed with a dilation stays in the relative ideal. -/
theorem isSoninPrincipalRelativeIdeal_correctionDiff_comp_dilation
    (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    IsSoninPrincipalRelativeIdeal
      ((evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) *
        evenDilationCLM r hr) :=
  ((IsSoninPrincipalRelativeIdeal.projectionCorrection a ha).sub
    (IsSoninPrincipalRelativeIdeal.projectionCorrection b hb)).rightMul _

/-- **The full error budget.**  Five terms: the vector's own projection correction, a correction
difference read through the dilation, the physical shell on the dilate, the dilate's two band terms,
and the vector's band content. -/
theorem norm_soninApertureCoupling_sub_dilate_le_budget
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace}
    (hlow : evenIndicatorCutoff b w = 0) (hhigh : evenIndicatorCutoff c w = w) :
    ‖evenSoninApertureSuccessiveLayerTransition a b c r hr w -
        evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w‖ ≤
      2 * ‖evenSoninProjectionCorrection b w‖ +
        ‖((evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) *
            evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))) w‖ +
        ‖(evenIndicatorCutoff b - evenIndicatorCutoff a)
          (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w)‖ +
        (‖evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w -
            evenFourierCutoff b (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w)‖ +
          ‖evenFourierCutoff a
            (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w)‖) +
        ‖evenFourierCutoff b w‖ := by
  set v : evenSubspace := evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w with hv
  have hbase := norm_soninApertureCoupling_sub_dilate_le hab hbc hr hcr hlow hhigh
  have hlayer := norm_evenSoninApertureLayer_sub_le a b v
  have hcomp : ((evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) *
      evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))) w =
      (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) v := rfl
  rw [hcomp]
  linarith [hbase, hlayer]

end RHTower

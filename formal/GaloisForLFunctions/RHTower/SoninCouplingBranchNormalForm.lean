import GaloisForLFunctions.RHTower.SoninInverseBranchVanishing

/-!
# Branch normal form of the layer coupling on the annulus

Assembling the two vanishing laws: on a vector living in the annulus between the two apertures the
Sonin projection splits into the vector, minus its Fourier band, plus a trace-class correction; the
aperture layer then sees only the expanding dilation of the first piece and only the contracting
one of the second.

The coupling therefore has a normal form in which each principal term carries a single dilation
branch, and the branches are opposite.  Everything that is not one of those two terms is trace
class.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **Branch normal form.**  On an annulus vector the coupling is the expanding dilation of the
vector, minus the contracting dilation of its Fourier band, plus a trace-class remainder. -/
theorem evenSoninApertureSuccessiveLayerTransition_apply_annulus_branches
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace}
    (hlow : evenIndicatorCutoff b w = 0) (hhigh : evenIndicatorCutoff c w = w) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr w =
      evenSoninApertureLayer a b
            (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w) -
          evenSoninApertureLayer a b
            (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w)) +
        evenSoninApertureLayer a b
          (evenDilationSum r hr (evenSoninProjectionCorrection b w)) := by
  have hbr : b ≤ r * a := hbc.trans hcr
  have hRb : evenFourierCutoff b (evenFourierCutoff b w) =
      evenFourierCutoff b w := by
    have hmul := evenFourierCutoff_mul_min b b
    rw [min_self] at hmul
    have := congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => T w) hmul
    simpa using this
  rw [evenSoninApertureSuccessiveLayerTransition_apply_annulus hbc hr hlow hhigh]
  have hsplit : evenDilationSum r hr
        ((w - evenFourierCutoff b w) + evenSoninProjectionCorrection b w) =
      (evenDilationSum r hr w -
          evenDilationSum r hr (evenFourierCutoff b w)) +
        evenDilationSum r hr (evenSoninProjectionCorrection b w) := by
    rw [map_add, map_sub]
  rw [hsplit, map_add, map_sub,
    evenSoninApertureLayer_evenDilationSum_apply_eq_inverse hab hr hcr hhigh,
    evenSoninApertureLayer_evenDilationSum_apply_eq_forward hab hr hbr hRb]

/-- With a vanishing correction the coupling on the annulus is exactly the difference of the two
opposite dilation branches. -/
theorem evenSoninApertureSuccessiveLayerTransition_apply_annulus_branches_of_correction_eq_zero
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace}
    (hlow : evenIndicatorCutoff b w = 0) (hhigh : evenIndicatorCutoff c w = w)
    (hcorr : evenSoninProjectionCorrection b w = 0) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr w =
      evenSoninApertureLayer a b
          (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w) -
        evenSoninApertureLayer a b
          (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w)) := by
  rw [evenSoninApertureSuccessiveLayerTransition_apply_annulus_branches
    hab hbc hr hcr hlow hhigh, hcorr, map_zero, map_zero, add_zero]

end RHTower

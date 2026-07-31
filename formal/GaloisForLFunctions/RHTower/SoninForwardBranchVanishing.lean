import GaloisForLFunctions.RHTower.SoninOuterBandProjectionSplit

/-!
# The forward dilation branch of the aperture layer vanishes on the inner band

Inside the crossing chamber the forward dilation contracts the outer window below the inner
aperture: a vector supported in `[-c,c]` is carried by `U_r` into `[-c/r, c/r]`, and `c <= r a`
makes that a subset of `[-a,a]`.  Both Sonin projections annihilate vectors supported inside their
own window, so the aperture layer kills the forward branch outright.

Only the inverse branch of the dilation therefore contributes to the layer coupling on the inner
band.  Combined with the outer-band split of the projection this removes one of the two dilation
directions from the coupling question.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The forward dilation carries the outer window inside the inner one. -/
theorem indicatorCutoff_evenDilationCLM_apply_of_indicatorCutoff_eq_self
    {a c r : ℝ} (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    evenIndicatorCutoff a (evenDilationCLM r (zero_lt_one.trans hr) w) =
      evenDilationCLM r (zero_lt_one.trans hr) w := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hmove := evenDilationCLM_mul_evenIndicatorCutoff c r hr0
  have hband : evenIndicatorCutoff (r⁻¹ * c)
      (evenDilationCLM r hr0 w) = evenDilationCLM r hr0 w := by
    have := congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => T w) hmove
    simp only [mul_apply_eq_comp] at this
    rw [hw] at this
    exact this.symm
  have hle : r⁻¹ * c ≤ a := by
    rw [inv_mul_le_iff₀ hr0]
    linarith [hcr]
  calc
    evenIndicatorCutoff a (evenDilationCLM r hr0 w)
        = evenIndicatorCutoff a (evenIndicatorCutoff (r⁻¹ * c)
            (evenDilationCLM r hr0 w)) := by rw [hband]
    _ = (evenIndicatorCutoff a * evenIndicatorCutoff (r⁻¹ * c))
          (evenDilationCLM r hr0 w) := rfl
    _ = evenIndicatorCutoff (r⁻¹ * c) (evenDilationCLM r hr0 w) := by
        rw [evenIndicatorCutoff_mul_min, min_eq_right hle]
    _ = evenDilationCLM r hr0 w := hband

/-- **Forward-branch vanishing.**  In the crossing chamber the aperture layer annihilates the
forward dilation of every inner-band vector. -/
theorem evenSoninApertureLayer_evenDilationCLM_apply_eq_zero
    {a b c r : ℝ} (hab : a ≤ b) (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    evenSoninApertureLayer a b
      (evenDilationCLM r (zero_lt_one.trans hr) w) = 0 := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hA : evenIndicatorCutoff a (evenDilationCLM r hr0 w) =
      evenDilationCLM r hr0 w :=
    indicatorCutoff_evenDilationCLM_apply_of_indicatorCutoff_eq_self hr hcr hw
  have hB : evenIndicatorCutoff b (evenDilationCLM r hr0 w) =
      evenDilationCLM r hr0 w := by
    calc
      evenIndicatorCutoff b (evenDilationCLM r hr0 w)
          = evenIndicatorCutoff b (evenIndicatorCutoff a
              (evenDilationCLM r hr0 w)) := by rw [hA]
      _ = (evenIndicatorCutoff b * evenIndicatorCutoff a)
            (evenDilationCLM r hr0 w) := rfl
      _ = evenIndicatorCutoff a (evenDilationCLM r hr0 w) := by
          rw [evenIndicatorCutoff_mul_min, min_eq_right hab]
      _ = evenDilationCLM r hr0 w := hA
  have hQa : evenCentralSoninProjection a (evenDilationCLM r hr0 w) = 0 :=
    evenCentralSoninProjection_eq_zero_of_indicatorCutoff_eq_self a hA
  have hQb : evenCentralSoninProjection b (evenDilationCLM r hr0 w) = 0 :=
    evenCentralSoninProjection_eq_zero_of_indicatorCutoff_eq_self b hB
  unfold evenSoninApertureLayer
  rw [sub_apply, hQa, hQb, sub_zero]

/-- **Only the inverse branch survives.**  On an inner-band vector the aperture layer sees the
dilation sum only through its inverse branch. -/
theorem evenSoninApertureLayer_evenDilationSum_apply_eq_inverse
    {a b c r : ℝ} (hab : a ≤ b) (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    evenSoninApertureLayer a b (evenDilationSum r hr w) =
      evenSoninApertureLayer a b
        (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w) := by
  rw [evenDilationSum_eq]
  have hsplit : (evenDilationCLM r (zero_lt_one.trans hr) +
      evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))) w =
      evenDilationCLM r (zero_lt_one.trans hr) w +
        evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w := rfl
  rw [hsplit, map_add,
    evenSoninApertureLayer_evenDilationCLM_apply_eq_zero (c := c) hab hr hcr hw,
    zero_add]

end RHTower

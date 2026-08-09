import GaloisForLFunctions.RHTower.ProlateDunsterDensityTransfer
import GaloisForLFunctions.RHTower.XiAmplitudeDecay
import GaloisForLFunctions.RHTower.XiCoordinate

/-!
# The integrated profile transfer

The pointwise transfer bounds the exact radial profile against the regular Bessel model by
`O(c^-1)` times the amplitude and the Bessel envelope.  Beyond the matching point the envelope is
at most one and the amplitude at most four, so the pointwise bound is a constant multiple of
`c^-1`, and integrating costs only the length of the range.

Combined with the compact-range primitive of the model, this transfers that primitive to the exact
profile.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- **The integrated transfer.**  On a range beyond the matching point the exact profile and the
regular Bessel model have primitives differing by `O(c^-1)` times the length. -/
theorem abs_integral_radialProlate_sub_besselProfile_le
    {s c a b : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hAa : dunsterEndpointCrossing c ≤ a) (hab : a ≤ b) :
    |∫ x in a..b, (R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x))|
      ≤ (4 * radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant / c)
        * (b - a) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  have hA1 : (1 : ℝ) < dunsterEndpointCrossing c := dunsterEndpointCrossing_gt_one hc0
  have hK : 0 ≤ radialProlateUniformTransferConstant := radialProlateUniformTransferConstant_nonneg
  have hC : 0 ≤ lgBesselCommonEnvelopeConstant := lgBesselCommonEnvelopeConstant_nonneg
  have hcross : 1 ≤ c * xiEndpointPhase s (dunsterEndpointCrossing c) :=
    one_le_c_mul_xiEndpointPhase_crossing hs0 hs1 hc
  have hpt : ∀ x ∈ Set.uIoc a b,
      ‖R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)‖
        ≤ 4 * radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant / c := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hAx : dunsterEndpointCrossing c ≤ x := le_trans hAa (le_of_lt hx.1)
    have hx1 : (1 : ℝ) < x := lt_of_lt_of_le hA1 hAx
    have hbase := abs_radialProlate_sub_besselProfile_le hs0 hs1 hc hR1 hR hDR hode hAx
    -- the envelope is at most one beyond the matching point
    have hphase : c * xiEndpointPhase s (dunsterEndpointCrossing c)
        ≤ c * xiEndpointPhase s x := by
      have := (strictMonoOn_xiEndpointPhase hs0 hs1).monotoneOn
        (mem_Ici.mpr (le_of_lt hA1)) (mem_Ici.mpr (le_of_lt hx1)) hAx
      nlinarith [this, hc0.le]
    have hone : (1 : ℝ) ≤ Real.sqrt (c * xiEndpointPhase s x) :=
      Real.one_le_sqrt.mpr (le_trans hcross hphase)
    have hsqpos : (0 : ℝ) < Real.sqrt (c * xiEndpointPhase s x) := by linarith
    have henv : lgBesselCommonEnvelopeConstant / Real.sqrt (c * xiEndpointPhase s x)
        ≤ lgBesselCommonEnvelopeConstant := by
      rw [div_le_iff₀ hsqpos]
      nlinarith [hC, hone]
    -- the amplitude is at most four
    have hamp : xiAmplitude s x ≤ 4 := by
      have h := xiAmplitude_le hs0 hs1 hx1
      have hsx : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr (le_of_lt hx1)
      have h2 : Real.sqrt (Real.sqrt 2) ≤ 2 := sqrt_sqrt_two_le_two
      have hq : Real.sqrt (Real.sqrt 2) / Real.sqrt x ≤ 4 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [h2, hsx]
      linarith
    have hamp0 : 0 ≤ xiAmplitude s x := (xiAmplitude_pos hs0 hs1 hx1).le
    rw [Real.norm_eq_abs]
    refine le_trans hbase ?_
    have hstep : xiAmplitude s x *
        ((radialProlateUniformTransferConstant / c) *
          (lgBesselCommonEnvelopeConstant / Real.sqrt (c * xiEndpointPhase s x)))
        ≤ 4 * ((radialProlateUniformTransferConstant / c) * lgBesselCommonEnvelopeConstant) := by
      have hinner : (radialProlateUniformTransferConstant / c) *
          (lgBesselCommonEnvelopeConstant / Real.sqrt (c * xiEndpointPhase s x))
          ≤ (radialProlateUniformTransferConstant / c) * lgBesselCommonEnvelopeConstant :=
        mul_le_mul_of_nonneg_left henv (by positivity)
      have hnn : 0 ≤ (radialProlateUniformTransferConstant / c) * lgBesselCommonEnvelopeConstant :=
        by positivity
      nlinarith [hinner, hamp, hamp0, hnn]
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h

end GaloisForLFunctions.RHTower

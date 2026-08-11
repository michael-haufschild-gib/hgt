import GaloisForLFunctions.RHTower.ProlateEnvelopeIntegral
import GaloisForLFunctions.RHTower.XiCompactPrimitive
import GaloisForLFunctions.HTGeometry.InteriorIntegrationByParts

/-!
# The compact-range primitive of the exact prolate profile

The model's primitive is `O(c^-1)` and the sharp transfer says the exact profile differs from the
model by `O(c^(-3/2))` in primitive, which the model's own `sqrt c` normalization turns into
`O(c^-1)` as well.  Adding them bounds the primitive of the *exact* normalized profile.

The profile is integrable up to the endpoint even though it has no value there: it is bounded and
continuous on the open interval, which is all that is needed.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- The regular Bessel profile is interval integrable up to the endpoint. -/
theorem intervalIntegrable_radialProlateBesselProfile {s c a b : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (radialProlateBesselProfile s c) volume a b := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine GaloisForLFunctions.HTGeometry.intervalIntegrable_of_continuousOn_Ioo_of_bounded
    hab ?_ (M := 2 * Real.sqrt c) ?_
  · have hsub : Ioo a b ⊆ Ioi 1 := fun x hx => lt_of_le_of_lt ha hx.1
    refine (continuousOn_const.mul ((continuousOn_xiAmplitude hs0 hs1).mono hsub)).mul ?_
    exact continuous_besselJ0'.comp_continuousOn
      (continuousOn_const.mul (((continuousOn_xiEndpointPhase hs0).mono hsub)))
  · intro x hx
    have hx1 : (1 : ℝ) < x := lt_of_le_of_lt ha hx.1
    have hamp : xiAmplitude s x ≤ 2 := by
      have h := xiAmplitude_le hs0 hs1 hx1
      have hsx : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr (le_of_lt hx1)
      have h2 : Real.sqrt (Real.sqrt 2) ≤ 2 := sqrt_sqrt_two_le_two
      have hq : Real.sqrt (Real.sqrt 2) / Real.sqrt x ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [h2, hsx]
      linarith
    have hamp0 : (0 : ℝ) ≤ xiAmplitude s x := (xiAmplitude_pos hs0 hs1 hx1).le
    have hJ := abs_besselJ0_le_one (c * xiEndpointPhase s x)
    rw [radialProlateBesselProfile, abs_mul, abs_mul, abs_of_pos hsc, abs_of_nonneg hamp0]
    have hprod : xiAmplitude s x * |besselJ0 (c * xiEndpointPhase s x)| ≤ 2 := by
      nlinarith [hJ, hamp, hamp0, abs_nonneg (besselJ0 (c * xiEndpointPhase s x))]
    calc Real.sqrt c * xiAmplitude s x * |besselJ0 (c * xiEndpointPhase s x)|
        = Real.sqrt c * (xiAmplitude s x * |besselJ0 (c * xiEndpointPhase s x)|) := by ring
      _ ≤ Real.sqrt c * 2 := mul_le_mul_of_nonneg_left hprod hsc.le
      _ = 2 * Real.sqrt c := by ring

/-- **The primitive of the exact normalized profile.**  On the compact exterior range beyond the
matching point the exact profile has primitive `O(c^-1)`, the same rate as the model. -/
theorem abs_integral_sqrt_mul_radialProlate_le
    {s c X : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hAX : dunsterEndpointCrossing c ≤ X) (hX2 : X ≤ 2) :
    |∫ x in (dunsterEndpointCrossing c)..X, Real.sqrt c * R x|
      ≤ (8 * radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant / 3
          + 2 * (648 * 64)) / c := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hss : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
  have hA1 : (1 : ℝ) < dunsterEndpointCrossing c := dunsterEndpointCrossing_gt_one hc0
  have hA2 : dunsterEndpointCrossing c ≤ 2 := by
    have := dunsterEndpointCrossing_le_eleven_tenths hc
    linarith
  set A : ℝ := dunsterEndpointCrossing c with hAdef
  -- integrability of the two pieces
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt
  have hsubIoi : Icc A X ⊆ Ioi 1 := fun x hx => lt_of_lt_of_le hA1 hx.1
  have hdiffc : ContinuousOn
      (fun x : ℝ => R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) (Icc A X) := by
    refine hRc.continuousOn.sub (((continuousOn_xiAmplitude hs0 hs1).mono hsubIoi).mul ?_)
    exact continuous_besselJ0'.comp_continuousOn
      (continuousOn_const.mul ((continuousOn_xiEndpointPhase hs0).mono hsubIoi))
  have hi1 : IntervalIntegrable
      (fun x : ℝ => R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) volume A X :=
    (Set.uIcc_of_le hAX ▸ hdiffc).intervalIntegrable
  have hi2 : IntervalIntegrable (radialProlateBesselProfile s c) volume A X :=
    intervalIntegrable_radialProlateBesselProfile hs0 hs1 hc0 (le_of_lt hA1) hAX
  -- decompose
  have hdecomp : (∫ x in A..X, Real.sqrt c * R x)
      = Real.sqrt c * (∫ x in A..X,
            (R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)))
        + ∫ x in A..X, radialProlateBesselProfile s c x := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (hi1.const_mul _) hi2]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [radialProlateBesselProfile]
    ring
  -- the transfer contribution
  have htrans := abs_integral_radialProlate_sub_besselProfile_sharp_le hs0 hs1 hc hR1 hR hDR hode
    (le_refl A) hAX hX2
  have hterm1 : |Real.sqrt c * (∫ x in A..X,
      (R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)))|
      ≤ 8 * radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant / (3 * c) := by
    rw [abs_mul, abs_of_pos hsc]
    have hstep := mul_le_mul_of_nonneg_left htrans hsc.le
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  -- the model contribution
  have hmodel : |∫ x in A..X, radialProlateBesselProfile s c x| ≤ 2 * (648 * 64) / c := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_radialProlateBesselProfile hs0 hs1 hc0 (le_refl 1) (le_of_lt hA1))
      hi2
    have h1 := abs_integral_radialProlateBesselProfile_le hs0 hs1 hA1 hA2 hc0
    have h2 := abs_integral_radialProlateBesselProfile_le hs0 hs1
      (lt_of_lt_of_le hA1 hAX) hX2 hc0
    have heq : (∫ x in A..X, radialProlateBesselProfile s c x)
        = (∫ x in (1 : ℝ)..X, radialProlateBesselProfile s c x)
          - ∫ x in (1 : ℝ)..A, radialProlateBesselProfile s c x := by
      linarith [hsplit]
    rw [heq]
    have := abs_sub (∫ x in (1 : ℝ)..X, radialProlateBesselProfile s c x)
      (∫ x in (1 : ℝ)..A, radialProlateBesselProfile s c x)
    have hval : (648 : ℝ) * 64 / c + 648 * 64 / c = 2 * (648 * 64) / c := by ring
    linarith [this, h1, h2, hval]
  rw [hdecomp]
  refine le_trans (abs_add_le _ _) ?_
  have hval2 : 8 * radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant / (3 * c)
      + 2 * (648 * 64) / c
      = (8 * radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant / 3
          + 2 * (648 * 64)) / c := by
    field_simp
  linarith [hterm1, hmodel, hval2.le, hval2.symm.le]

end GaloisForLFunctions.RHTower

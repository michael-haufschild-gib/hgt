import GaloisForLFunctions.RHTower.ProlateProfileTransferIntegral
import GaloisForLFunctions.HTGeometry.InverseSqrtEndpointIntegral
import GaloisForLFunctions.RHTower.AmpFourthDecay

/-!
# The transfer error keeps its rate under integration

Bounding the Bessel envelope by one loses half a power of the frequency.  The envelope decays like
`(c xi_sigma(x))^{-1/2}`, and the phase itself is at least `sqrt(x-1)` near the endpoint, so the
envelope is integrable against the endpoint singularity `(x-1)^{-1/4}` and contributes a further
`c^{-1/2}`.

Keeping that decay is what preserves the rate: the transfer error integrates to `O(c^{-3/2})`, which
after the model's own `sqrt c` normalization is `O(c^{-1})` — the same rate as the primitive of the
model itself.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- **The phase dominates the endpoint square root.**  A clean consequence of the corpus bracket:
the two constants `sqrt(1-s) >= sqrt(1/2)` and `sqrt(x+1) >= sqrt 2` cancel exactly. -/
theorem sqrt_sub_one_le_xiEndpointPhase {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 ≤ x) :
    Real.sqrt (x - 1) ≤ xiEndpointPhase s x := by
  have hm1 : (0 : ℝ) ≤ x - 1 := by linarith
  have hp1 : (0 : ℝ) ≤ x + 1 := by linarith
  have hbase := (xiEndpointPhase_bounds hs0 (by linarith) hx).1
  have hsplit : Real.sqrt (x ^ 2 - 1) = Real.sqrt (x - 1) * Real.sqrt (x + 1) := by
    rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring, Real.sqrt_mul hm1]
  have h1s : Real.sqrt (1 / 2) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt 2 ≤ Real.sqrt (x + 1) := Real.sqrt_le_sqrt (by linarith)
  have hprod : Real.sqrt (1 / 2) * Real.sqrt 2 = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have hkey : Real.sqrt (x - 1) ≤ Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1) := by
    rw [hsplit]
    calc Real.sqrt (x - 1)
        = Real.sqrt (1 / 2) * Real.sqrt 2 * Real.sqrt (x - 1) := by rw [hprod]; ring
      _ ≤ Real.sqrt (1 - s) * Real.sqrt (x + 1) * Real.sqrt (x - 1) := by
          gcongr
      _ = Real.sqrt (1 - s) * (Real.sqrt (x - 1) * Real.sqrt (x + 1)) := by ring
  linarith [hkey, hbase]

/-- The quarter-power endpoint weight has bounded integral on the compact exterior range. -/
theorem integral_rpow_neg_quarter_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    (∫ x in a..b, (x - 1) ^ (-(1 : ℝ) / 4)) ≤ 4 / 3 := by
  have hint : ∀ u v : ℝ, 1 ≤ u → u ≤ v →
      IntervalIntegrable (fun t : ℝ => (t - 1) ^ (-(1 : ℝ) / 4)) volume u v := by
    intro u v _ _
    have hbase : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ) / 4)) volume (u - 1) (v - 1) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h := hbase.comp_sub_right 1
    simpa using h
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint 1 a le_rfl ha) (hint a b ha hab)
  have hnn : 0 ≤ ∫ x in (1 : ℝ)..a, (x - 1) ^ (-(1 : ℝ) / 4) := by
    refine intervalIntegral.integral_nonneg ha fun x hx => ?_
    exact Real.rpow_nonneg (by linarith [hx.1]) _
  have htot : (∫ x in (1 : ℝ)..b, (x - 1) ^ (-(1 : ℝ) / 4))
      = (4 / 3) * (b - 1) ^ ((3 : ℝ) / 4) :=
    GaloisForLFunctions.HTGeometry.integral_rpow_neg_quarter_sub_one (le_trans ha hab)
  have hpow : (b - 1) ^ ((3 : ℝ) / 4) ≤ 1 := by
    refine Real.rpow_le_one (by linarith) (by linarith) (by norm_num)
  rw [htot] at hsplit
  nlinarith [hsplit, hnn, hpow]

/-- The Bessel envelope is dominated by the quarter-power endpoint weight, with the frequency's own
half power extracted. -/
theorem envelope_le_quarter_weight {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hx : 1 < x) :
    lgBesselCommonEnvelopeConstant / Real.sqrt (c * xiEndpointPhase s x)
      ≤ (lgBesselCommonEnvelopeConstant / Real.sqrt c) * (x - 1) ^ (-(1 : ℝ) / 4) := by
  have hC : 0 ≤ lgBesselCommonEnvelopeConstant := lgBesselCommonEnvelopeConstant_nonneg
  have hm1 : (0 : ℝ) < x - 1 := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hphase : Real.sqrt (x - 1) ≤ xiEndpointPhase s x :=
    sqrt_sub_one_le_xiEndpointPhase hs0 hs1 (le_of_lt hx)
  have hq : (0 : ℝ) < Real.sqrt (Real.sqrt (x - 1)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hm1)
  have hroot : Real.sqrt (Real.sqrt (x - 1)) ≤ Real.sqrt (xiEndpointPhase s x) :=
    Real.sqrt_le_sqrt hphase
  have hsplit : Real.sqrt (c * xiEndpointPhase s x)
      = Real.sqrt c * Real.sqrt (xiEndpointPhase s x) := Real.sqrt_mul hc.le _
  have hden : Real.sqrt c * Real.sqrt (Real.sqrt (x - 1))
      ≤ Real.sqrt (c * xiEndpointPhase s x) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hroot hsc.le
  have hdpos : (0 : ℝ) < Real.sqrt c * Real.sqrt (Real.sqrt (x - 1)) := by positivity
  have hval : (lgBesselCommonEnvelopeConstant / Real.sqrt c) * (x - 1) ^ (-(1 : ℝ) / 4)
      = lgBesselCommonEnvelopeConstant / (Real.sqrt c * Real.sqrt (Real.sqrt (x - 1))) := by
    rw [GaloisForLFunctions.HTGeometry.rpow_neg_quarter_eq_inv_sqrt_sqrt hm1.le]
    field_simp
  rw [hval]
  exact div_le_div_of_nonneg_left hC hdpos hden


/-- **The sharp integrated transfer.**  Retaining the envelope's decay, the transfer error
integrates to `O(c^{-3/2})` on the compact exterior range -- one half power better than the crude
bound, which is exactly what the model's `sqrt c` normalization consumes. -/
theorem abs_integral_radialProlate_sub_besselProfile_sharp_le
    {s c a b : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hAa : dunsterEndpointCrossing c ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    |∫ x in a..b, (R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x))|
      ≤ 8 * radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant
          / (3 * c * Real.sqrt c) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hA1 : (1 : ℝ) < dunsterEndpointCrossing c := dunsterEndpointCrossing_gt_one hc0
  have ha1 : (1 : ℝ) < a := lt_of_lt_of_le hA1 hAa
  have hK : 0 ≤ radialProlateUniformTransferConstant := radialProlateUniformTransferConstant_nonneg
  have hC : 0 ≤ lgBesselCommonEnvelopeConstant := lgBesselCommonEnvelopeConstant_nonneg
  set K : ℝ := radialProlateUniformTransferConstant with hKdef
  set C : ℝ := lgBesselCommonEnvelopeConstant with hCdef
  -- continuity of the difference on the range
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt
  have hsubIoi : Set.Icc a b ⊆ Set.Ioi 1 := fun x hx => lt_of_lt_of_le ha1 hx.1
  have hfc : ContinuousOn
      (fun x : ℝ => R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x))
      (Set.Icc a b) := by
    refine hRc.continuousOn.sub (((continuousOn_xiAmplitude hs0 hs1).mono hsubIoi).mul ?_)
    refine continuous_besselJ0.comp_continuousOn (continuousOn_const.mul ?_)
    exact (continuousOn_xiEndpointPhase hs0).mono hsubIoi
  have hgc : ContinuousOn (fun x : ℝ => 2 * K * C / (c * Real.sqrt c) * (x - 1) ^ (-(1 : ℝ) / 4))
      (Set.Icc a b) := by
    refine continuousOn_const.mul (ContinuousOn.rpow_const ?_ fun x hx => ?_)
    · exact continuousOn_id.sub continuousOn_const
    · exact Or.inl (ne_of_gt (by have := Set.mem_Ioi.mp (hsubIoi hx); linarith))
  have hi1 : IntervalIntegrable
      (fun x : ℝ => |R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)|) volume a b :=
    ((Set.uIcc_of_le hab ▸ hfc).abs).intervalIntegrable
  have hi2 : IntervalIntegrable
      (fun x : ℝ => 2 * K * C / (c * Real.sqrt c) * (x - 1) ^ (-(1 : ℝ) / 4)) volume a b :=
    (Set.uIcc_of_le hab ▸ hgc).intervalIntegrable
  -- pointwise bound
  have hpt : ∀ x ∈ Set.Icc a b,
      |R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)|
        ≤ 2 * K * C / (c * Real.sqrt c) * (x - 1) ^ (-(1 : ℝ) / 4) := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hsubIoi hx
    have hAx : dunsterEndpointCrossing c ≤ x := le_trans hAa hx.1
    have hbase := abs_radialProlate_sub_besselProfile_le hs0 hs1 hc hR1 hR hDR hode hAx
    have hamp : xiAmplitude s x ≤ 2 := by
      have h := xiAmplitude_le hs0 hs1 hx1
      have hsx : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr (le_of_lt hx1)
      have h2 : Real.sqrt (Real.sqrt 2) ≤ 2 := sqrt_sqrt_two_le_two
      have hq : Real.sqrt (Real.sqrt 2) / Real.sqrt x ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [h2, hsx]
      linarith
    have hamp0 : (0 : ℝ) ≤ xiAmplitude s x := (xiAmplitude_pos hs0 hs1 hx1).le
    have henv := envelope_le_quarter_weight hs0 hs1 hc0 hx1
    have hpow0 : (0 : ℝ) ≤ (x - 1) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_nonneg (by linarith) _
    refine le_trans hbase ?_
    have hstep : xiAmplitude s x * ((K / c) * (C / Real.sqrt (c * xiEndpointPhase s x)))
        ≤ 2 * ((K / c) * ((C / Real.sqrt c) * (x - 1) ^ (-(1 : ℝ) / 4))) := by
      have hKc : (0 : ℝ) ≤ K / c := div_nonneg hK hc0.le
      have hCc : (0 : ℝ) ≤ C / Real.sqrt c := div_nonneg hC hsc.le
      have hinner : (K / c) * (C / Real.sqrt (c * xiEndpointPhase s x))
          ≤ (K / c) * ((C / Real.sqrt c) * (x - 1) ^ (-(1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left henv hKc
      have hnn : (0 : ℝ) ≤ (K / c) * ((C / Real.sqrt c) * (x - 1) ^ (-(1 : ℝ) / 4)) :=
        mul_nonneg hKc (mul_nonneg hCc hpow0)
      nlinarith [hinner, hamp, hamp0, hnn]
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  -- integrate
  have hmono : (∫ x in a..b, |R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)|)
      ≤ ∫ x in a..b, 2 * K * C / (c * Real.sqrt c) * (x - 1) ^ (-(1 : ℝ) / 4) :=
    intervalIntegral.integral_mono_on hab hi1 hi2 hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have hweight := integral_rpow_neg_quarter_le (le_of_lt ha1) hab hb
  have hnn : (0 : ℝ) ≤ 2 * K * C / (c * Real.sqrt c) :=
    div_nonneg (by nlinarith [hK, hC]) (by positivity)
  have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f :=
    fun x : ℝ => R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) hab
  have hfin : 2 * K * C / (c * Real.sqrt c) * (∫ x in a..b, (x - 1) ^ (-(1 : ℝ) / 4))
      ≤ 2 * K * C / (c * Real.sqrt c) * (4 / 3) :=
    mul_le_mul_of_nonneg_left hweight hnn
  have hval : 2 * K * C / (c * Real.sqrt c) * (4 / 3)
      = 8 * K * C / (3 * c * Real.sqrt c) := by
    field_simp
    ring
  calc |∫ x in a..b, (R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x))|
      ≤ ∫ x in a..b, |R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)| := habs
    _ ≤ 2 * K * C / (c * Real.sqrt c) * (∫ x in a..b, (x - 1) ^ (-(1 : ℝ) / 4)) := hmono
    _ ≤ 2 * K * C / (c * Real.sqrt c) * (4 / 3) := hfin
    _ = 8 * K * C / (3 * c * Real.sqrt c) := hval


/-- **The phase grows linearly on the exterior range.**  A sharper companion to
`sqrt_sub_one_le_xiEndpointPhase`, which is the right bound only near the endpoint. -/
theorem half_mul_le_xiEndpointPhase {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    x / 2 ≤ xiEndpointPhase s x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hd : (0 : ℝ) ≤ x ^ 2 - 1 := by nlinarith
  have hs : (0 : ℝ) ≤ 1 - s := by linarith
  have hbase := (xiEndpointPhase_bounds hs0 (by linarith) (by linarith : (1 : ℝ) ≤ x)).1
  have hprod : x / 2 ≤ Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1) := by
    have hnn : (0 : ℝ) ≤ Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1) := by positivity
    have hsq : (Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1)) ^ 2 = (1 - s) * (x ^ 2 - 1) := by
      rw [mul_pow, Real.sq_sqrt hs, Real.sq_sqrt hd]
    have hgoal : (x / 2) ^ 2 ≤ (Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1)) ^ 2 := by
      rw [hsq]
      nlinarith [hx, hs1, hs0]
    nlinarith [hgoal, hnn, hx0]
  linarith [hbase, hprod]


/-- **The bridge error, with its decay in `x` made explicit.**  The packaged constant
`compactBesselProfileError` freezes this at the left endpoint; the underlying bound decays. -/
theorem abs_profile_sub_model_decay_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hx : 2 ≤ x) (hcxi : 1 ≤ c * xiEndpointPhase s x) :
    |Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)
        - Real.sqrt (2 / Real.pi) * ampFourth s x
          * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)|
      ≤ 10 / (x * Real.sqrt (Real.sqrt (c * x / 2))) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hbase := abs_profile_sub_model_le hs0 hs1 (by linarith : (1 : ℝ) < x) hc hcxi
  have hamp := ampFourth_le_two_div hs0 hs1 hx
  have hphase := half_mul_le_xiEndpointPhase hs0 hs1 hx
  have hcx : (0 : ℝ) < c * x / 2 := by positivity
  have hmono : c * x / 2 ≤ c * xiEndpointPhase s x := by
    have := mul_le_mul_of_nonneg_left hphase hc.le
    linarith [this]
  have hroot : Real.sqrt (Real.sqrt (c * x / 2))
      ≤ Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) :=
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hmono)
  have hrpos : (0 : ℝ) < Real.sqrt (Real.sqrt (c * x / 2)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hcx)
  refine le_trans hbase ?_
  have hnum : 5 * ampFourth s x ≤ 10 / x := by
    have h := mul_le_mul_of_nonneg_left hamp (by norm_num : (0 : ℝ) ≤ 5)
    calc 5 * ampFourth s x ≤ 5 * (2 / x) := h
      _ = 10 / x := by ring
  have hden : 0 < Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
    refine Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ?_)
    linarith [hmono, hcx]
  calc 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x))
      ≤ (10 / x) / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
        gcongr
    _ ≤ (10 / x) / Real.sqrt (Real.sqrt (c * x / 2)) := by
        gcongr
    _ = 10 / (x * Real.sqrt (Real.sqrt (c * x / 2))) := by
        rw [div_div]


end GaloisForLFunctions.RHTower

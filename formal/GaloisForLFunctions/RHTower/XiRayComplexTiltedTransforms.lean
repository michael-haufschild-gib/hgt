import GaloisForLFunctions.RHTower.XiBezoutianSeparatedRealPacketPosSemidef

/-!
# Tilted transforms: the centered Xi logarithmic derivative near the real Euler ray

The bilateral Laplace transform of the theta-cusp source is perturbed off the real ray by an
imaginary tilt `t` through the oscillation factor `e^{itx} − 1`, whose modulus is at most
`|t||x|`.  Together with the absolute first and second Laplace moments — both controlled by
powers of `log b` times the transform itself — this yields, inside the explicit tilt budget
`|t| ≤ 1/(32(log b + 3))`, two-sided control of the centered Xi logarithmic derivative off
the ray: `(log b)/16 ≤ Re L(b + it)` and `‖L(b + it)‖ ≤ 4 log b`.  These are the complex
inputs for the tilted-packet positivity of the Bezoutian criterion matrices.
-/

open Complex Real MeasureTheory Set
open scoped ComplexOrder

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-! ## Oscillation and component bounds -/

private theorem norm_exp_real_mul_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ |θ| := by
  have hre : (Complex.exp ((θ : ℂ) * Complex.I) - 1).re = Real.cos θ - 1 := by
    rw [Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have him : (Complex.exp ((θ : ℂ) * Complex.I) - 1).im = Real.sin θ := by
    rw [Complex.exp_mul_I]
    simp [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  have hsq : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    have := Real.sin_sq_add_cos_sq θ
    nlinarith
  have hbound : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 ≤ θ ^ 2 := by
    rw [hsq]
    have := Real.one_sub_sq_div_two_le_cos (x := θ)
    nlinarith
  have h1 : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖
      = Real.sqrt (‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2) :=
    (Real.sqrt_sq (norm_nonneg _)).symm
  rw [h1]
  calc Real.sqrt (‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2)
      ≤ Real.sqrt (θ ^ 2) := Real.sqrt_le_sqrt hbound
    _ = |θ| := Real.sqrt_sq_eq_abs θ

private theorem abs_re_le_norm' (z : ℂ) : |z.re| ≤ ‖z‖ := by
  rcases abs_cases z.re with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    exact Complex.re_le_norm z
  · rw [h]
    have := Complex.re_le_norm (-z)
    simpa using this

private theorem abs_im_le_norm' (z : ℂ) : |z.im| ≤ ‖z‖ := by
  rcases abs_cases z.im with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    exact Complex.im_le_norm z
  · rw [h]
    have := Complex.im_le_norm (-z)
    simpa using this

/-! ## Absolute and second Laplace moments -/

/-- Absolute first Laplace moment of the theta-cusp source. -/
def xiRayLaplaceAbsMoment (b : ℝ) : ℝ :=
  ∫ x : ℝ, |x| * thetaCuspFullSource x * Real.exp (b * x)

/-- Second Laplace moment of the theta-cusp source. -/
def xiRayLaplaceSecondMoment (b : ℝ) : ℝ :=
  ∫ x : ℝ, x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)

theorem integrable_xiRayLaplaceAbsMoment (b : ℝ) :
    Integrable (fun x : ℝ => |x| * thetaCuspFullSource x * Real.exp (b * x)) := by
  have hmaj := HedenmalmThetaSource.integrable_abs_mul_exp_abs_mul_thetaCuspFullSource |b|
  apply Integrable.mono hmaj
  · exact ((continuous_abs.mul contDiff_thetaCuspFullSource.continuous).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards with x
    have hΦ : 0 ≤ thetaCuspFullSource x := (thetaCuspFullSource_pos x).le
    have hnn : 0 ≤ |x| * thetaCuspFullSource x * Real.exp (b * x) :=
      mul_nonneg (mul_nonneg (abs_nonneg x) hΦ) (Real.exp_pos _).le
    have hmajnn : 0 ≤ |x| * Real.exp (|b| * |x|) * thetaCuspFullSource x :=
      mul_nonneg (mul_nonneg (abs_nonneg x) (Real.exp_pos _).le) hΦ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg hmajnn]
    have he : Real.exp (b * x) ≤ Real.exp (|b| * |x|) := by
      apply Real.exp_le_exp.mpr
      calc b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
    calc |x| * thetaCuspFullSource x * Real.exp (b * x)
        ≤ |x| * thetaCuspFullSource x * Real.exp (|b| * |x|) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg x) hΦ)
      _ = |x| * Real.exp (|b| * |x|) * thetaCuspFullSource x := by ring

private theorem sq_le_four_mul_exp_abs (x : ℝ) : x ^ 2 ≤ 4 * Real.exp |x| := by
  have h1 : |x| / 2 ≤ Real.exp (|x| / 2) := by
    have := Real.add_one_le_exp (|x| / 2)
    linarith
  have h2 : |x| ≤ 2 * Real.exp (|x| / 2) := by linarith
  have h3 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have h4 : |x| ^ 2 ≤ (2 * Real.exp (|x| / 2)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg x) h2 2
  have h5 : (2 * Real.exp (|x| / 2)) ^ 2 = 4 * Real.exp |x| := by
    have he : Real.exp (|x| / 2) ^ 2 = Real.exp |x| := by
      rw [← Real.exp_nat_mul]
      norm_num
      ring_nf
    rw [mul_pow, he]
    norm_num
  linarith [h3 ▸ h4, h5 ▸ h4]

theorem integrable_xiRayLaplaceSecondMoment (b : ℝ) :
    Integrable (fun x : ℝ => x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)) := by
  have hmaj := (HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource
    (|b| + 1)).const_mul 4
  apply Integrable.mono hmaj
  · exact (((continuous_pow 2).mul contDiff_thetaCuspFullSource.continuous).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards with x
    have hΦ : 0 ≤ thetaCuspFullSource x := (thetaCuspFullSource_pos x).le
    have hnn : 0 ≤ x ^ 2 * thetaCuspFullSource x * Real.exp (b * x) :=
      mul_nonneg (mul_nonneg (sq_nonneg x) hΦ) (Real.exp_pos _).le
    have hmajnn : 0 ≤ 4 * (Real.exp ((|b| + 1) * |x|) * thetaCuspFullSource x) := by
      have := mul_nonneg (Real.exp_pos ((|b| + 1) * |x|)).le hΦ
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg hmajnn]
    have he : Real.exp (b * x) ≤ Real.exp (|b| * |x|) := by
      apply Real.exp_le_exp.mpr
      calc b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
    have hx2 := sq_le_four_mul_exp_abs x
    calc x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)
        ≤ (4 * Real.exp |x|) * thetaCuspFullSource x * Real.exp (|b| * |x|) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hx2 hΦ
          · exact he
          · exact (Real.exp_pos _).le
          · exact mul_nonneg (by positivity) hΦ
      _ = 4 * (Real.exp ((|b| + 1) * |x|) * thetaCuspFullSource x) := by
          rw [show (|b| + 1) * |x| = |b| * |x| + |x| by ring, Real.exp_add]
          ring

/-! ## Comparison of the moments with the transform -/

private theorem exp_one_pow_le (k : ℕ) (c : ℝ)
    (h : (2.7182818286 : ℝ) ^ k ≤ c) : Real.exp (k : ℝ) ≤ c := by
  have h1 : Real.exp ((k : ℝ)) = (Real.exp 1) ^ k := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 : (Real.exp 1) ^ k ≤ (2.7182818286 : ℝ) ^ k :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le k
  linarith

theorem thetaEnvelopeUpper_le_xiRayLaplace {b : ℝ} (hb : xiRayPacketBase ≤ b) :
    thetaEnvelopeUpper ≤ xiRayLaplace b := by
  have hR := xiRayPacketBase_ge
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hfloor := xiRayLaplace_ge hb0
  have hE2 : HedenmalmThetaSource.thetaEnvelope 2
      = Real.exp (9 - Real.pi * Real.exp 4) := by
    unfold HedenmalmThetaSource.thetaEnvelope
    rw [← Real.exp_add]
    norm_num
    ring_nf
  have hbRu : Real.pi * Real.exp 4 + Real.log xiRayEnvelopeRatio + 12 ≤ b := by
    have h1 := xiRayUpperBase_le_packetBase
    have : xiRayUpperBase = Real.pi * Real.exp 4 + Real.log xiRayEnvelopeRatio + 12 := rfl
    linarith
  have hkey : xiRayEnvelopeRatio ≤ Real.exp (9 - Real.pi * Real.exp 4 + b) := by
    have h1 : Real.log xiRayEnvelopeRatio ≤ 9 - Real.pi * Real.exp 4 + b := by linarith
    calc xiRayEnvelopeRatio
        = Real.exp (Real.log xiRayEnvelopeRatio) := (Real.exp_log xiRayEnvelopeRatio_pos).symm
      _ ≤ Real.exp (9 - Real.pi * Real.exp 4 + b) := Real.exp_le_exp.mpr h1
  have hCu : thetaEnvelopeUpper = xiRayEnvelopeRatio * thetaEnvelopeLower :=
    thetaEnvelopeUpper_eq_ratio_mul
  have hchain : thetaEnvelopeUpper
      ≤ thetaEnvelopeLower * HedenmalmThetaSource.thetaEnvelope 2 * Real.exp b := by
    rw [hCu, hE2]
    have h2 : thetaEnvelopeLower * Real.exp (9 - Real.pi * Real.exp 4) * Real.exp b
        = thetaEnvelopeLower * Real.exp (9 - Real.pi * Real.exp 4 + b) := by
      rw [mul_assoc, ← Real.exp_add]
    rw [h2]
    calc xiRayEnvelopeRatio * thetaEnvelopeLower
        ≤ Real.exp (9 - Real.pi * Real.exp 4 + b) * thetaEnvelopeLower :=
          mul_le_mul_of_nonneg_right hkey thetaEnvelopeLower_pos.le
      _ = thetaEnvelopeLower * Real.exp (9 - Real.pi * Real.exp 4 + b) := by ring
  linarith

theorem xiRayLaplaceAbsMoment_le {b : ℝ} (hb : xiRayPacketBase ≤ b) :
    xiRayLaplaceAbsMoment b ≤ (Real.log b + 3) * xiRayLaplace b := by
  have hR := xiRayPacketBase_ge
  have hb0 : (0 : ℝ) < b := by linarith
  have hZpos := xiRayLaplace_pos hb0.le
  -- split |x| into the two half lines
  have hint := integrable_xiRayLaplaceAbsMoment b
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hint
  rw [compl_Ioi] at hsplit
  have hpos_eq : (∫ x in Ioi (0 : ℝ), |x| * thetaCuspFullSource x * Real.exp (b * x))
      = ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (b * x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [abs_of_pos hx0]
  have hneg_eq : (∫ x in Iic (0 : ℝ), |x| * thetaCuspFullSource x * Real.exp (b * x))
      = ∫ x in Iic (0 : ℝ), (-x) * thetaCuspFullSource x * Real.exp (b * x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro x hx
    have hx0 : x ≤ (0 : ℝ) := hx
    simp only [abs_of_nonpos hx0]
  -- the reflected negative half line
  have hreflect : (∫ x in Iic (0 : ℝ), (-x) * thetaCuspFullSource x * Real.exp (b * x))
      = ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x)) := by
    have h := integral_comp_neg_Iic (0 : ℝ)
      (fun u => u * thetaCuspFullSource u * Real.exp (-(b * u)))
    have hL : (fun x : ℝ => (-x) * thetaCuspFullSource (-x) * Real.exp (-(b * -x)))
        = fun x : ℝ => (-x) * thetaCuspFullSource x * Real.exp (b * x) := by
      funext x
      rw [thetaCuspFullSource_neg]
      ring_nf
    rw [neg_zero] at h
    calc (∫ x in Iic (0 : ℝ), (-x) * thetaCuspFullSource x * Real.exp (b * x))
        = ∫ x in Iic (0 : ℝ), (-x) * thetaCuspFullSource (-x) * Real.exp (-(b * -x)) := by
          rw [hL]
      _ = ∫ u in Ioi (0 : ℝ), u * thetaCuspFullSource u * Real.exp (-(b * u)) := h
  have hnegle : (∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x)))
      ≤ thetaEnvelopeUpper := moment_reflected_le hb0
  -- the positive half line via the moment identity
  have hposle : (∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (b * x))
      ≤ xiRayLaplaceMoment b + thetaEnvelopeUpper := by
    have hmsplit := moment_even_split b
    have hA'0 : 0 ≤ ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x)) :=
      setIntegral_nonneg measurableSet_Ioi fun x hx =>
        mul_nonneg (mul_nonneg (le_of_lt hx) (thetaCuspFullSource_pos x).le)
          (Real.exp_pos _).le
    linarith [hnegle]
  have hN : xiRayLaplaceMoment b ≤ (Real.log b + 1) * xiRayLaplace b := by
    have h := xiRayLaplaceLogDeriv_le (le_trans xiRayUpperBase_le_packetBase hb)
    have h2 : xiRayLaplaceMoment b = xiRayLaplaceLogDeriv b * xiRayLaplace b := by
      unfold xiRayLaplaceLogDeriv
      rw [div_mul_cancel₀ _ (ne_of_gt hZpos)]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h hZpos.le
  have hCuZ := thetaEnvelopeUpper_le_xiRayLaplace hb
  have htotal : xiRayLaplaceAbsMoment b
      = (∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (b * x))
        + ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x)) := by
    unfold xiRayLaplaceAbsMoment
    rw [← hsplit, hpos_eq, hneg_eq, hreflect]
  calc xiRayLaplaceAbsMoment b
      = (∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (b * x))
        + ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x)) := htotal
    _ ≤ (xiRayLaplaceMoment b + thetaEnvelopeUpper) + thetaEnvelopeUpper := by
        linarith [hposle, hnegle]
    _ ≤ (Real.log b + 1) * xiRayLaplace b + xiRayLaplace b + xiRayLaplace b := by
        linarith [hN, hCuZ]
    _ = (Real.log b + 3) * xiRayLaplace b := by ring

end RHTower

namespace RHTower

open HedenmalmThetaSource

/-! ## The second-moment comparison -/

set_option maxHeartbeats 1600000 in
theorem xiRayLaplaceSecondMoment_le {b : ℝ} (hb : xiRayPacketBase ≤ b) :
    xiRayLaplaceSecondMoment b ≤ (Real.log b + 3) ^ 2 * xiRayLaplace b := by
  have hR := xiRayPacketBase_ge
  have hγ1 := one_le_xiRayEnvelopeRatio
  have hγ0 := xiRayEnvelopeRatio_pos
  have hCl := thetaEnvelopeLower_pos
  have hCu := thetaEnvelopeUpper_pos
  have hb0 : (0 : ℝ) < b := by linarith
  have hZpos := xiRayLaplace_pos hb0.le
  set X := Real.log b with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef, Real.le_log_iff_exp_le hb0]
    have := Real.exp_one_lt_d9
    linarith
  have hX0 : 0 < X := by linarith
  have hXb : X ≤ b - 1 := by
    rw [hXdef]
    exact Real.log_le_sub_one_of_pos hb0
  have hint := integrable_xiRayLaplaceSecondMoment b
  have hsplit : (∫ x in Iic X, x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)) +
      (∫ x in Ioi X, x ^ 2 * thetaCuspFullSource x * Real.exp (b * x))
      = xiRayLaplaceSecondMoment b := by
    have h := MeasureTheory.integral_add_compl (measurableSet_Iic (a := X)) hint
    rwa [compl_Iic] at h
  have hsplit2 : (∫ x in Iic (-X), x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)) +
      (∫ x in Ioc (-X) X, x ^ 2 * thetaCuspFullSource x * Real.exp (b * x))
      = ∫ x in Iic X, x ^ 2 * thetaCuspFullSource x * Real.exp (b * x) := by
    have hu : Iic (-X) ∪ Ioc (-X) X = Iic X := Iic_union_Ioc_eq_Iic (by linarith)
    rw [← hu, MeasureTheory.setIntegral_union (by
        rw [Set.disjoint_left]
        intro t ht ht'
        exact absurd ht'.1 (not_lt.mpr ht)) measurableSet_Ioc
      hint.integrableOn hint.integrableOn]
  have hmid : (∫ x in Ioc (-X) X, x ^ 2 * thetaCuspFullSource x * Real.exp (b * x))
      ≤ X ^ 2 * xiRayLaplace b := by
    have hmono : (∫ x in Ioc (-X) X, x ^ 2 * thetaCuspFullSource x * Real.exp (b * x))
        ≤ ∫ x in Ioc (-X) X, X ^ 2 * (thetaCuspFullSource x * Real.exp (b * x)) := by
      apply MeasureTheory.setIntegral_mono_on
        hint.integrableOn
        (((integrable_xiRayLaplace b).const_mul (X ^ 2)).integrableOn)
        measurableSet_Ioc
      intro x hx
      have hx2 : x ^ 2 ≤ X ^ 2 := sq_le_sq' (by linarith [hx.1]) hx.2
      have h0 : 0 ≤ thetaCuspFullSource x * Real.exp (b * x) :=
        mul_nonneg (thetaCuspFullSource_pos x).le (Real.exp_pos _).le
      calc x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)
          = x ^ 2 * (thetaCuspFullSource x * Real.exp (b * x)) := by ring
        _ ≤ X ^ 2 * (thetaCuspFullSource x * Real.exp (b * x)) :=
            mul_le_mul_of_nonneg_right hx2 h0
    have h2 : (∫ x in Ioc (-X) X, X ^ 2 * (thetaCuspFullSource x * Real.exp (b * x)))
        = X ^ 2 * ∫ x in Ioc (-X) X, thetaCuspFullSource x * Real.exp (b * x) :=
      MeasureTheory.integral_const_mul _ _
    have h3 : (∫ x in Ioc (-X) X, thetaCuspFullSource x * Real.exp (b * x))
        ≤ xiRayLaplace b :=
      MeasureTheory.setIntegral_le_integral (integrable_xiRayLaplace b)
        (Filter.Eventually.of_forall fun x =>
          mul_nonneg (thetaCuspFullSource_pos x).le (Real.exp_pos _).le)
    calc (∫ x in Ioc (-X) X, x ^ 2 * thetaCuspFullSource x * Real.exp (b * x))
        ≤ X ^ 2 * ∫ x in Ioc (-X) X, thetaCuspFullSource x * Real.exp (b * x) := by
          rw [← h2]
          exact hmono
      _ ≤ X ^ 2 * xiRayLaplace b := mul_le_mul_of_nonneg_left h3 (sq_nonneg X)
  have hleft : (∫ x in Iic (-X), x ^ 2 * thetaCuspFullSource x * Real.exp (b * x))
      ≤ 4 * xiRayLaplace b := by
    have hreflect : (∫ x in Iic (-X), x ^ 2 * thetaCuspFullSource x * Real.exp (b * x))
        = ∫ u in Ioi X, u ^ 2 * thetaCuspFullSource u * Real.exp (-(b * u)) := by
      have h := integral_comp_neg_Iic (-X)
        (fun u => u ^ 2 * thetaCuspFullSource u * Real.exp (-(b * u)))
      have hL : (fun x : ℝ => (-x) ^ 2 * thetaCuspFullSource (-x) * Real.exp (-(b * -x)))
          = fun x : ℝ => x ^ 2 * thetaCuspFullSource x * Real.exp (b * x) := by
        funext x
        rw [thetaCuspFullSource_neg]
        ring_nf
      rw [neg_neg] at h
      calc (∫ x in Iic (-X), x ^ 2 * thetaCuspFullSource x * Real.exp (b * x))
          = ∫ x in Iic (-X),
              (-x) ^ 2 * thetaCuspFullSource (-x) * Real.exp (-(b * -x)) := by
            rw [hL]
        _ = ∫ u in Ioi X, u ^ 2 * thetaCuspFullSource u * Real.exp (-(b * u)) := h
    have hintneg : Integrable (fun x : ℝ =>
        x ^ 2 * thetaCuspFullSource x * Real.exp (-(b * x))) := by
      apply (integrable_xiRayLaplaceSecondMoment (-b)).congr
      filter_upwards with x
      rw [neg_mul]
    have hsub : (∫ u in Ioi X, u ^ 2 * thetaCuspFullSource u * Real.exp (-(b * u)))
        ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * thetaCuspFullSource u * Real.exp (-(b * u)) := by
      apply MeasureTheory.setIntegral_mono_set hintneg.integrableOn
        (Filter.Eventually.of_forall fun u => mul_nonneg (mul_nonneg (sq_nonneg u)
          (thetaCuspFullSource_pos u).le) (Real.exp_pos _).le)
        (LE.le.eventuallyLE (Ioi_subset_Ioi hX0.le))
    have hb1 : (0 : ℝ) < b - 1 := by linarith
    have hintmass : Integrable (fun x : ℝ =>
        thetaCuspFullSource x * Real.exp (-((b - 1) * x))) := by
      apply (integrable_xiRayLaplace (-(b - 1))).congr
      filter_upwards with x
      rw [neg_mul]
    have hpoint : ∀ u ∈ Ioi (0 : ℝ),
        u ^ 2 * thetaCuspFullSource u * Real.exp (-(b * u))
          ≤ 4 * (thetaCuspFullSource u * Real.exp (-((b - 1) * u))) := by
      intro u hu
      have hu0 : (0 : ℝ) < u := hu
      have h2 := sq_le_four_mul_exp_abs u
      rw [abs_of_pos hu0] at h2
      have hΦ0 : 0 ≤ thetaCuspFullSource u := (thetaCuspFullSource_pos u).le
      have hexp : Real.exp u * Real.exp (-(b * u)) = Real.exp (-((b - 1) * u)) := by
        rw [← Real.exp_add]
        ring_nf
      calc u ^ 2 * thetaCuspFullSource u * Real.exp (-(b * u))
          ≤ (4 * Real.exp u) * thetaCuspFullSource u * Real.exp (-(b * u)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right h2 hΦ0
        _ = 4 * (thetaCuspFullSource u * (Real.exp u * Real.exp (-(b * u)))) := by ring
        _ = 4 * (thetaCuspFullSource u * Real.exp (-((b - 1) * u))) := by rw [hexp]
    have hint4 : (∫ u in Ioi (0 : ℝ), u ^ 2 * thetaCuspFullSource u * Real.exp (-(b * u)))
        ≤ ∫ u in Ioi (0 : ℝ), 4 * (thetaCuspFullSource u * Real.exp (-((b - 1) * u))) :=
      MeasureTheory.setIntegral_mono_on hintneg.integrableOn
        ((hintmass.const_mul 4).integrableOn) measurableSet_Ioi hpoint
    have hconst : (∫ u in Ioi (0 : ℝ), 4 * (thetaCuspFullSource u * Real.exp (-((b - 1) * u))))
        = 4 * ∫ u in Ioi (0 : ℝ), thetaCuspFullSource u * Real.exp (-((b - 1) * u)) :=
      MeasureTheory.integral_const_mul _ _
    have hmass : (∫ u in Ioi (0 : ℝ), thetaCuspFullSource u * Real.exp (-((b - 1) * u)))
        ≤ thetaEnvelopeUpper := mass_reflected_le hb1
    have hCuZ := thetaEnvelopeUpper_le_xiRayLaplace hb
    rw [hreflect]
    calc (∫ u in Ioi X, u ^ 2 * thetaCuspFullSource u * Real.exp (-(b * u)))
        ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * thetaCuspFullSource u * Real.exp (-(b * u)) := hsub
      _ ≤ ∫ u in Ioi (0 : ℝ), 4 * (thetaCuspFullSource u * Real.exp (-((b - 1) * u))) := hint4
      _ = 4 * ∫ u in Ioi (0 : ℝ), thetaCuspFullSource u * Real.exp (-((b - 1) * u)) := hconst
      _ ≤ 4 * thetaEnvelopeUpper := by linarith [hmass]
      _ ≤ 4 * xiRayLaplace b := by linarith [hCuZ]
  -- right tail
  have hb2 : Real.exp (2 * X) = b ^ 2 := by
    rw [hXdef, two_mul, Real.exp_add, Real.exp_log hb0]
    ring
  have hrate : b + 9 / 2 + 3 ≤ 2 * Real.pi * b ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have htailpoint : ∀ x ∈ Ioi X,
      x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)
        ≤ (thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) ^ 2)
            * (Real.exp X * Real.exp (-x)) := by
    intro x hx
    have hxX : X < x := hx
    have hx0 : 0 < x := lt_trans hX0 hxX
    have hΦ := thetaCuspFullSource_le_envelope hx0.le
    have hexp2x : b ^ 2 * (1 + 2 * (x - X)) ≤ Real.exp (2 * x) := by
      have h1 : Real.exp (2 * x) = Real.exp (2 * X) * Real.exp (2 * (x - X)) := by
        rw [← Real.exp_add]
        ring_nf
      have h2 : 1 + 2 * (x - X) ≤ Real.exp (2 * (x - X)) := by
        have := Real.add_one_le_exp (2 * (x - X))
        linarith
      rw [h1, hb2]
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg b)
    have hexponent : (b + 9 / 2) * x - Real.pi * Real.exp (2 * x)
        ≤ (b + 9 / 2) * X - Real.pi * b ^ 2
          - (2 * Real.pi * b ^ 2 - (b + 9 / 2)) * (x - X) := by
      have hπ := Real.pi_pos
      nlinarith [hexp2x]
    have hlin : x ^ 2 * Real.exp (-((2 * Real.pi * b ^ 2 - (b + 9 / 2)) * (x - X)))
        ≤ (X + 1) ^ 2 * Real.exp (-(x - X)) := by
      set u := x - X with hu
      have hu0 : 0 < u := by rw [hu]; linarith
      set r := 2 * Real.pi * b ^ 2 - (b + 9 / 2) with hr
      have hr3 : 3 ≤ r := by rw [hr]; linarith [hrate]
      have hx' : x = X + u := by rw [hu]; ring
      have h1 : (X + u) ^ 2 ≤ (X + 1) ^ 2 * (1 + u) ^ 2 := by
        have hle : X + u ≤ (X + 1) * (1 + u) := by
          nlinarith [mul_nonneg hX0.le hu0.le]
        have h0 : (0 : ℝ) ≤ X + u := by linarith
        calc (X + u) ^ 2 ≤ ((X + 1) * (1 + u)) ^ 2 := pow_le_pow_left₀ h0 hle 2
          _ = (X + 1) ^ 2 * (1 + u) ^ 2 := by ring
      have h2 : (1 + u) ^ 2 ≤ Real.exp (2 * u) := by
        have ha := Real.add_one_le_exp u
        have hc : Real.exp u ^ 2 = Real.exp (2 * u) := by
          rw [pow_two, ← Real.exp_add, two_mul]
        have hb' : (1 + u) ^ 2 ≤ Real.exp u ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith
      have h3 : Real.exp (2 * u) ≤ Real.exp ((r - 1) * u) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h4 : (X + u) ^ 2 ≤ (X + 1) ^ 2 * Real.exp ((r - 1) * u) := by
        calc (X + u) ^ 2 ≤ (X + 1) ^ 2 * (1 + u) ^ 2 := h1
          _ ≤ (X + 1) ^ 2 * Real.exp (2 * u) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ ≤ (X + 1) ^ 2 * Real.exp ((r - 1) * u) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : (X + 1) ^ 2 * Real.exp ((r - 1) * u) * Real.exp (-(r * u))
          = (X + 1) ^ 2 * Real.exp (-u) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      calc x ^ 2 * Real.exp (-(r * u)) = (X + u) ^ 2 * Real.exp (-(r * u)) := by rw [hx']
        _ ≤ (X + 1) ^ 2 * Real.exp ((r - 1) * u) * Real.exp (-(r * u)) :=
            mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
        _ = (X + 1) ^ 2 * Real.exp (-u) := h5
    have hΦe : x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)
        ≤ thetaEnvelopeUpper *
            (x ^ 2 * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))) := by
      have hpack : thetaEnvelope x * Real.exp (b * x)
          = Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x)) := by
        unfold HedenmalmThetaSource.thetaEnvelope
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
      have h1 : thetaCuspFullSource x * Real.exp (b * x)
          ≤ thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x)) := by
        rw [← hpack, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hΦ (Real.exp_pos _).le
      calc x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)
          = x ^ 2 * (thetaCuspFullSource x * Real.exp (b * x)) := by ring
        _ ≤ x ^ 2 *
              (thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg x)
        _ = thetaEnvelopeUpper *
              (x ^ 2 * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))) := by ring
    have hmid2 : x ^ 2 * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))
        ≤ Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
            * ((X + 1) ^ 2 * Real.exp (-(x - X))) := by
      have h1 : Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))
          ≤ Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
              * Real.exp (-((2 * Real.pi * b ^ 2 - (b + 9 / 2)) * (x - X))) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith [hexponent]
      calc x ^ 2 * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))
          ≤ x ^ 2 * (Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
              * Real.exp (-((2 * Real.pi * b ^ 2 - (b + 9 / 2)) * (x - X)))) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg x)
        _ = Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
              * (x ^ 2 * Real.exp (-((2 * Real.pi * b ^ 2 - (b + 9 / 2)) * (x - X)))) := by
            ring
        _ ≤ Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
              * ((X + 1) ^ 2 * Real.exp (-(x - X))) :=
            mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
    have hExX : Real.exp (-(x - X)) = Real.exp X * Real.exp (-x) := by
      rw [← Real.exp_add]
      ring_nf
    calc x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)
        ≤ thetaEnvelopeUpper *
            (x ^ 2 * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))) := hΦe
      _ ≤ thetaEnvelopeUpper * (Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
            * ((X + 1) ^ 2 * Real.exp (-(x - X)))) :=
          mul_le_mul_of_nonneg_left hmid2 thetaEnvelopeUpper_pos.le
      _ = (thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) ^ 2)
            * (Real.exp X * Real.exp (-x)) := by
          rw [hExX]
          ring
  have hmajint : IntegrableOn
      (fun x : ℝ =>
        (thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) ^ 2)
          * (Real.exp X * Real.exp (-x))) (Ioi X) := by
    have h1 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi X) := by
      have h0 := integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) X
      exact MeasureTheory.IntegrableOn.congr_fun h0
        (fun x _ => by simp only [neg_one_mul]) measurableSet_Ioi
    exact ((h1.const_mul _).const_mul _)
  have htail : (∫ x in Ioi X, x ^ 2 * thetaCuspFullSource x * Real.exp (b * x))
      ≤ thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) ^ 2 := by
    have hTle := MeasureTheory.setIntegral_mono_on
      hint.integrableOn hmajint measurableSet_Ioi htailpoint
    have hval : (∫ x in Ioi X,
        (thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) ^ 2)
          * (Real.exp X * Real.exp (-x)))
        = thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
      have h2 : (∫ x in Ioi X, Real.exp X * Real.exp (-x))
          = Real.exp X * ∫ x in Ioi X, Real.exp (-x) :=
        MeasureTheory.integral_const_mul _ _
      rw [h2, integral_exp_neg_Ioi, ← Real.exp_add]
      simp
    rw [hval] at hTle
    exact hTle
  have hTZ : thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) ^ 2
      ≤ xiRayLaplace b := by
    have hfloor := xiRayLaplace_ge hb0.le
    have hE2 : thetaEnvelope 2 = Real.exp (9 - Real.pi * Real.exp 4) := by
      unfold HedenmalmThetaSource.thetaEnvelope
      rw [← Real.exp_add]
      norm_num
      ring_nf
    have hXe : (X + 1) ^ 2 ≤ Real.exp (2 * X) := by
      have ha : X + 1 ≤ Real.exp X := by
        have := Real.add_one_le_exp X
        linarith
      have hc : Real.exp X ^ 2 = Real.exp (2 * X) := by
        rw [pow_two, ← Real.exp_add, two_mul]
      have hb' : (X + 1) ^ 2 ≤ Real.exp X ^ 2 :=
        pow_le_pow_left₀ (by linarith) ha 2
      linarith
    have hCuγ : thetaEnvelopeUpper = xiRayEnvelopeRatio * thetaEnvelopeLower :=
      thetaEnvelopeUpper_eq_ratio_mul
    have hbRu : Real.pi * Real.exp 4 + Real.log xiRayEnvelopeRatio + 12 ≤ b := by
      have h1 := xiRayUpperBase_le_packetBase
      have h2 : xiRayUpperBase = Real.pi * Real.exp 4 + Real.log xiRayEnvelopeRatio + 12 := rfl
      linarith
    have hexpineq : Real.log xiRayEnvelopeRatio
        + ((b + 9 / 2) * X - Real.pi * b ^ 2 + 2 * X)
        ≤ 9 - Real.pi * Real.exp 4 + b := by
      have h1 : (b + 9 / 2 + 2) * X ≤ 2 * b * (b - 1) := by
        have ha : b + 9 / 2 + 2 ≤ 2 * b := by linarith
        have hbb : (b + 9 / 2 + 2) * X ≤ 2 * b * X :=
          mul_le_mul_of_nonneg_right ha hX0.le
        have hcc : 2 * b * X ≤ 2 * b * (b - 1) :=
          mul_le_mul_of_nonneg_left hXb (by linarith)
        linarith
      have h2 : 3 * b ^ 2 ≤ Real.pi * b ^ 2 := by
        nlinarith [Real.pi_gt_three, sq_nonneg b]
      have h3 : b ≤ b ^ 2 := by nlinarith
      linarith [h1, h2, h3, hbRu]
    have hchain : thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
        * (X + 1) ^ 2
        ≤ thetaEnvelopeLower * thetaEnvelope 2 * Real.exp b := by
      have hLHS : thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
          * (X + 1) ^ 2
          ≤ thetaEnvelopeLower *
              (Real.exp (Real.log xiRayEnvelopeRatio)
                * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * Real.exp (2 * X)) := by
        rw [hCuγ, Real.exp_log xiRayEnvelopeRatio_pos]
        calc xiRayEnvelopeRatio * thetaEnvelopeLower
            * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) ^ 2
            ≤ xiRayEnvelopeRatio * thetaEnvelopeLower
              * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * Real.exp (2 * X) := by
              apply mul_le_mul_of_nonneg_left hXe
              have h0 : (0 : ℝ) ≤ xiRayEnvelopeRatio * thetaEnvelopeLower :=
                mul_nonneg hγ0.le hCl.le
              exact mul_nonneg h0 (Real.exp_pos _).le
          _ = thetaEnvelopeLower * (xiRayEnvelopeRatio
              * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * Real.exp (2 * X)) := by ring
      have hpack : Real.exp (Real.log xiRayEnvelopeRatio)
          * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * Real.exp (2 * X)
          = Real.exp (Real.log xiRayEnvelopeRatio
              + ((b + 9 / 2) * X - Real.pi * b ^ 2 + 2 * X)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
      have hRHS : Real.exp (Real.log xiRayEnvelopeRatio
          + ((b + 9 / 2) * X - Real.pi * b ^ 2 + 2 * X))
          ≤ Real.exp (9 - Real.pi * Real.exp 4 + b) :=
        Real.exp_le_exp.mpr hexpineq
      have hfin : thetaEnvelopeLower * thetaEnvelope 2 * Real.exp b
          = thetaEnvelopeLower * Real.exp (9 - Real.pi * Real.exp 4 + b) := by
        rw [hE2, mul_assoc]
        simp only [← Real.exp_add]
      calc thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) ^ 2
          ≤ thetaEnvelopeLower *
              (Real.exp (Real.log xiRayEnvelopeRatio)
                * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * Real.exp (2 * X)) := hLHS
        _ = thetaEnvelopeLower * Real.exp (Real.log xiRayEnvelopeRatio
              + ((b + 9 / 2) * X - Real.pi * b ^ 2 + 2 * X)) := by rw [hpack]
        _ ≤ thetaEnvelopeLower * Real.exp (9 - Real.pi * Real.exp 4 + b) :=
            mul_le_mul_of_nonneg_left hRHS hCl.le
        _ = thetaEnvelopeLower * thetaEnvelope 2 * Real.exp b := hfin.symm
    linarith
  -- total
  have hfin2 : (X ^ 2 + 5) * xiRayLaplace b ≤ (X + 3) ^ 2 * xiRayLaplace b := by
    apply mul_le_mul_of_nonneg_right _ hZpos.le
    nlinarith
  have := hXdef
  linarith [hsplit, hsplit2, hmid, hleft, htail, hTZ, hfin2]

end RHTower

namespace RHTower

open HedenmalmThetaSource

/-! ## Tilt perturbation of the bilateral transforms -/

theorem norm_thetaBilateralLaplace_tilt_sub_le (b t : ℝ) :
    ‖thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I) - ((xiRayLaplace b : ℝ) : ℂ)‖
      ≤ |t| * xiRayLaplaceAbsMoment b := by
  have hbase : ((xiRayLaplace b : ℝ) : ℂ)
      = ∫ x : ℝ, (thetaCuspFullSource x : ℂ) * Complex.exp ((b : ℂ) * (x : ℂ)) := by
    rw [← xiCent_ofReal, ← thetaBilateralLaplace_eq_xiCent, thetaBilateralLaplace_eq_integral]
  have hfun : (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * Complex.exp (((b : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ))
        - (thetaCuspFullSource x : ℂ) * Complex.exp ((b : ℂ) * (x : ℂ)))
      = fun x : ℝ => ((thetaCuspFullSource x * Real.exp (b * x) : ℝ) : ℂ)
          * (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) := by
    funext x
    have hsplit : Complex.exp (((b : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ))
        = Complex.exp ((b : ℂ) * (x : ℂ)) * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    push_cast
    ring
  rw [thetaBilateralLaplace_eq_integral, hbase,
    ← MeasureTheory.integral_sub (integrable_thetaBilateralLaplace _)
      (integrable_thetaBilateralLaplace _), hfun]
  have hintnorm : Integrable (fun x : ℝ =>
      ‖((thetaCuspFullSource x * Real.exp (b * x) : ℝ) : ℂ)
        * (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1)‖) := by
    have h1 : Integrable (fun x : ℝ =>
        (thetaCuspFullSource x : ℂ) * Complex.exp (((b : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ))
          - (thetaCuspFullSource x : ℂ) * Complex.exp ((b : ℂ) * (x : ℂ))) :=
      (integrable_thetaBilateralLaplace _).sub (integrable_thetaBilateralLaplace _)
    have h2 := h1.norm
    apply h2.congr
    filter_upwards with x
    exact congrArg norm (congrFun hfun x)
  calc ‖∫ x : ℝ, ((thetaCuspFullSource x * Real.exp (b * x) : ℝ) : ℂ)
        * (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1)‖
      ≤ ∫ x : ℝ, ‖((thetaCuspFullSource x * Real.exp (b * x) : ℝ) : ℂ)
          * (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, |t| * (|x| * thetaCuspFullSource x * Real.exp (b * x)) := by
        apply MeasureTheory.integral_mono hintnorm
          ((integrable_xiRayLaplaceAbsMoment b).const_mul |t|)
        intro x
        dsimp only
        have hΦe : 0 ≤ thetaCuspFullSource x * Real.exp (b * x) :=
          mul_nonneg (thetaCuspFullSource_pos x).le (Real.exp_pos _).le
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΦe]
        have hosc := norm_exp_real_mul_I_sub_one_le (t * x)
        calc thetaCuspFullSource x * Real.exp (b * x)
              * ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖
            ≤ thetaCuspFullSource x * Real.exp (b * x) * |t * x| :=
              mul_le_mul_of_nonneg_left hosc hΦe
          _ = |t| * (|x| * thetaCuspFullSource x * Real.exp (b * x)) := by
              rw [abs_mul]
              ring
    _ = |t| * xiRayLaplaceAbsMoment b := by
        rw [MeasureTheory.integral_const_mul]
        rfl

theorem norm_thetaBilateralLaplaceMoment_tilt_sub_le (b t : ℝ) :
    ‖thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)
        - ((xiRayLaplaceMoment b : ℝ) : ℂ)‖
      ≤ |t| * xiRayLaplaceSecondMoment b := by
  have hbase : ((xiRayLaplaceMoment b : ℝ) : ℂ)
      = ∫ x : ℝ, (x : ℂ) * (thetaCuspFullSource x : ℂ) * Complex.exp ((b : ℂ) * (x : ℂ)) := by
    rw [← deriv_xiCent_ofReal, ← thetaBilateralLaplaceMoment_eq_deriv_xiCent]
    rfl
  have hfun : (fun x : ℝ =>
      (x : ℂ) * (thetaCuspFullSource x : ℂ)
          * Complex.exp (((b : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ))
        - (x : ℂ) * (thetaCuspFullSource x : ℂ) * Complex.exp ((b : ℂ) * (x : ℂ)))
      = fun x : ℝ => ((x * thetaCuspFullSource x * Real.exp (b * x) : ℝ) : ℂ)
          * (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) := by
    funext x
    have hsplit : Complex.exp (((b : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ))
        = Complex.exp ((b : ℂ) * (x : ℂ)) * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    push_cast
    ring
  unfold thetaBilateralLaplaceMoment
  rw [hbase, ← MeasureTheory.integral_sub (integrable_thetaBilateralLaplaceMoment _)
      (integrable_thetaBilateralLaplaceMoment _), hfun]
  have hintnorm : Integrable (fun x : ℝ =>
      ‖((x * thetaCuspFullSource x * Real.exp (b * x) : ℝ) : ℂ)
        * (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1)‖) := by
    have h1 : Integrable (fun x : ℝ =>
        (x : ℂ) * (thetaCuspFullSource x : ℂ)
            * Complex.exp (((b : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ))
          - (x : ℂ) * (thetaCuspFullSource x : ℂ) * Complex.exp ((b : ℂ) * (x : ℂ))) :=
      (integrable_thetaBilateralLaplaceMoment _).sub (integrable_thetaBilateralLaplaceMoment _)
    have h2 := h1.norm
    apply h2.congr
    filter_upwards with x
    exact congrArg norm (congrFun hfun x)
  calc ‖∫ x : ℝ, ((x * thetaCuspFullSource x * Real.exp (b * x) : ℝ) : ℂ)
        * (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1)‖
      ≤ ∫ x : ℝ, ‖((x * thetaCuspFullSource x * Real.exp (b * x) : ℝ) : ℂ)
          * (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, |t| * (x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)) := by
        apply MeasureTheory.integral_mono hintnorm
          ((integrable_xiRayLaplaceSecondMoment b).const_mul |t|)
        intro x
        dsimp only
        have hΦe : 0 ≤ thetaCuspFullSource x * Real.exp (b * x) :=
          mul_nonneg (thetaCuspFullSource_pos x).le (Real.exp_pos _).le
        have habs : |x * thetaCuspFullSource x * Real.exp (b * x)|
            = |x| * (thetaCuspFullSource x * Real.exp (b * x)) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (thetaCuspFullSource_pos x).le,
            abs_of_nonneg (Real.exp_pos _).le]
          ring
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, habs]
        have hosc := norm_exp_real_mul_I_sub_one_le (t * x)
        have h0 : 0 ≤ |x| * (thetaCuspFullSource x * Real.exp (b * x)) :=
          mul_nonneg (abs_nonneg x) hΦe
        calc |x| * (thetaCuspFullSource x * Real.exp (b * x))
              * ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖
            ≤ |x| * (thetaCuspFullSource x * Real.exp (b * x)) * |t * x| :=
              mul_le_mul_of_nonneg_left hosc h0
          _ = |t| * (|x| * |x| * (thetaCuspFullSource x * Real.exp (b * x))) := by
              rw [abs_mul]
              ring
          _ = |t| * (x ^ 2 * thetaCuspFullSource x * Real.exp (b * x)) := by
              rw [abs_mul_abs_self]
              ring
    _ = |t| * xiRayLaplaceSecondMoment b := by
        rw [MeasureTheory.integral_const_mul]
        rfl

theorem norm_thetaBilateralLaplaceMoment_tilt_le (b t : ℝ) :
    ‖thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ xiRayLaplaceAbsMoment b := by
  unfold thetaBilateralLaplaceMoment
  have hpoint : (fun x : ℝ => ‖(x : ℂ) * (thetaCuspFullSource x : ℂ)
      * Complex.exp (((b : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ))‖)
      = fun x : ℝ => |x| * thetaCuspFullSource x * Real.exp (b * x) := by
    funext x
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_exp]
    have hre : ((((b : ℂ) + (t : ℂ) * Complex.I)) * (x : ℂ)).re = b * x := by
      simp [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [hre, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (thetaCuspFullSource_pos x).le]
  calc ‖∫ x : ℝ, (x : ℂ) * (thetaCuspFullSource x : ℂ)
        * Complex.exp (((b : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ))‖
      ≤ ∫ x : ℝ, ‖(x : ℂ) * (thetaCuspFullSource x : ℂ)
          * Complex.exp (((b : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = xiRayLaplaceAbsMoment b := by
        rw [hpoint]
        rfl

end RHTower

namespace RHTower

/-! ## The tilt budget and the off-ray logarithmic-derivative bounds -/

/-- Imaginary-displacement budget for the tilted-packet positivity. -/
def xiRayTiltBudget (b : ℝ) : ℝ := 1 / (32 * (Real.log b + 3))

theorem xiRayTiltBudget_pos {b : ℝ} (hb : 1 ≤ b) : 0 < xiRayTiltBudget b := by
  unfold xiRayTiltBudget
  have h := Real.log_nonneg hb
  positivity

set_option maxHeartbeats 1600000 in
private theorem logDeriv_tilted_re_norm {b t : ℝ} (hb : xiRayPacketBase ≤ b)
    (ht : |t| ≤ xiRayTiltBudget b) :
    Real.log b / 16 ≤ (logDeriv xiCent ((b : ℂ) + (t : ℂ) * Complex.I)).re ∧
      ‖logDeriv xiCent ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4 * Real.log b := by
  have hR := xiRayPacketBase_ge
  have hb0 : (0 : ℝ) < b := by linarith
  have hZ := xiRayLaplace_pos hb0.le
  have hX5 : 5 ≤ Real.log b := by
    rw [Real.le_log_iff_exp_le hb0]
    have h1 : Real.exp ((5 : ℕ) : ℝ) ≤ 256 := exp_one_pow_le 5 256 (by norm_num)
    have h2 : ((5 : ℕ) : ℝ) = 5 := by norm_num
    rw [h2] at h1
    linarith
  have hX0 : (0 : ℝ) < Real.log b := by linarith
  have hX3 : (0 : ℝ) < Real.log b + 3 := by linarith
  -- budget consequences
  have ht' : |t| ≤ 1 / (32 * (Real.log b + 3)) := ht
  have habs := xiRayLaplaceAbsMoment_le hb
  have hsec := xiRayLaplaceSecondMoment_le hb
  have habs0 : 0 ≤ xiRayLaplaceAbsMoment b :=
    MeasureTheory.integral_nonneg fun x =>
      mul_nonneg (mul_nonneg (abs_nonneg x) (thetaCuspFullSource_pos x).le)
        (Real.exp_pos _).le
  have hsec0 : 0 ≤ xiRayLaplaceSecondMoment b :=
    MeasureTheory.integral_nonneg fun x =>
      mul_nonneg (mul_nonneg (sq_nonneg x) (thetaCuspFullSource_pos x).le)
        (Real.exp_pos _).le
  have hbudZ : |t| * xiRayLaplaceAbsMoment b ≤ xiRayLaplace b / 32 := by
    have h1 : |t| * xiRayLaplaceAbsMoment b
        ≤ (1 / (32 * (Real.log b + 3))) * ((Real.log b + 3) * xiRayLaplace b) := by
      apply mul_le_mul ht' habs habs0
      positivity
    have h2 : (1 / (32 * (Real.log b + 3))) * ((Real.log b + 3) * xiRayLaplace b)
        = xiRayLaplace b / 32 := by
      field_simp
    linarith
  have hbudN : |t| * xiRayLaplaceSecondMoment b
      ≤ (Real.log b + 3) * xiRayLaplace b / 32 := by
    have h1 : |t| * xiRayLaplaceSecondMoment b
        ≤ (1 / (32 * (Real.log b + 3))) * ((Real.log b + 3) ^ 2 * xiRayLaplace b) := by
      apply mul_le_mul ht' hsec hsec0
      positivity
    have h2 : (1 / (32 * (Real.log b + 3))) * ((Real.log b + 3) ^ 2 * xiRayLaplace b)
        = (Real.log b + 3) * xiRayLaplace b / 32 := by
      field_simp
    linarith
  have hZc_sub : ‖thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)
      - ((xiRayLaplace b : ℝ) : ℂ)‖ ≤ xiRayLaplace b / 32 :=
    le_trans (norm_thetaBilateralLaplace_tilt_sub_le b t) hbudZ
  have hNc_sub : ‖thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)
      - ((xiRayLaplaceMoment b : ℝ) : ℂ)‖ ≤ (Real.log b + 3) * xiRayLaplace b / 32 :=
    le_trans (norm_thetaBilateralLaplaceMoment_tilt_sub_le b t) hbudN
  have hNc_norm : ‖thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (Real.log b + 3) * xiRayLaplace b :=
    le_trans (norm_thetaBilateralLaplaceMoment_tilt_le b t) habs
  -- component bounds
  have hreZ : |(thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).re - xiRayLaplace b|
      ≤ xiRayLaplace b / 32 := by
    have h := abs_re_le_norm' (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)
      - ((xiRayLaplace b : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    linarith [hZc_sub]
  have himZ : |(thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).im|
      ≤ xiRayLaplace b / 32 := by
    have h := abs_im_le_norm' (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)
      - ((xiRayLaplace b : ℝ) : ℂ))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    linarith [hZc_sub]
  have hreN : |(thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).re
      - xiRayLaplaceMoment b| ≤ (Real.log b + 3) * xiRayLaplace b / 32 := by
    have h := abs_re_le_norm' (thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)
      - ((xiRayLaplaceMoment b : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    linarith [hNc_sub]
  have himN : |(thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).im|
      ≤ (Real.log b + 3) * xiRayLaplace b / 32 := by
    have h := abs_im_le_norm' (thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)
      - ((xiRayLaplaceMoment b : ℝ) : ℂ))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    linarith [hNc_sub]
  have hN_lower : Real.log b / 8 * xiRayLaplace b ≤ xiRayLaplaceMoment b := by
    have h := xiRayLaplaceLogDeriv_ge (le_trans xiRayLowerBase_le_packetBase hb)
    have h2 : xiRayLaplaceMoment b = xiRayLaplaceLogDeriv b * xiRayLaplace b := by
      unfold xiRayLaplaceLogDeriv
      rw [div_mul_cancel₀ _ (ne_of_gt hZ)]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h hZ.le
  have hreZlo : 31 / 32 * xiRayLaplace b
      ≤ (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).re := by
    have := abs_le.mp hreZ
    linarith [this.1]
  have hreZhi : (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).re
      ≤ 33 / 32 * xiRayLaplace b := by
    have := abs_le.mp hreZ
    linarith [this.2]
  have hreNlo : 3 * (Real.log b - 1) / 32 * xiRayLaplace b
      ≤ (thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).re := by
    have := abs_le.mp hreN
    have h1 := this.1
    nlinarith [hN_lower, hZ.le]
  have hreN0 : 0 ≤ (thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).re := by
    have h1 : (0 : ℝ) ≤ 3 * (Real.log b - 1) / 32 * xiRayLaplace b := by
      apply mul_nonneg _ hZ.le
      linarith
    linarith [hreNlo]
  -- normSq bounds
  have hnsq_hi : Complex.normSq (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I))
      ≤ 1090 / 1024 * xiRayLaplace b ^ 2 := by
    rw [Complex.normSq_apply]
    have h1 : (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).re ^ 2
        ≤ (33 / 32 * xiRayLaplace b) ^ 2 := by
      apply sq_le_sq' _ hreZhi
      have h0 : (0 : ℝ) ≤ 31 / 32 * xiRayLaplace b := by positivity
      linarith [hreZlo]
    have h2 : (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).im ^ 2
        ≤ (xiRayLaplace b / 32) ^ 2 := by
      have := abs_le.mp himZ
      exact sq_le_sq' (by linarith [this.1]) this.2
    nlinarith [hZ.le]
  have hnsq_lo : 961 / 1024 * xiRayLaplace b ^ 2
      ≤ Complex.normSq (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [Complex.normSq_apply]
    have h1 : (31 / 32 * xiRayLaplace b) ^ 2
        ≤ (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).re ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hreZlo
    nlinarith [sq_nonneg (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).im]
  have hZcne : thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    rw [h0, Complex.normSq_zero] at hnsq_lo
    nlinarith [hZ]
  have hLid : logDeriv xiCent ((b : ℂ) + (t : ℂ) * Complex.I)
      = thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)
        / thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I) := by
    rw [logDeriv_apply, ← thetaBilateralLaplaceMoment_eq_deriv_xiCent,
      ← thetaBilateralLaplace_eq_xiCent]
  constructor
  · -- real-part lower bound
    rw [hLid, Complex.div_re, ← add_div]
    have hnum : (92 * Real.log b - 96) / 1024 * xiRayLaplace b ^ 2
        ≤ (thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).re
            * (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).re
          + (thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).im
            * (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).im := by
      have hprod1 : (3 * (Real.log b - 1) / 32 * xiRayLaplace b)
          * (31 / 32 * xiRayLaplace b)
          ≤ (thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).re
            * (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).re := by
        apply mul_le_mul hreNlo hreZlo (by positivity) hreN0
      have hprod2 : -((Real.log b + 3) * xiRayLaplace b / 32 * (xiRayLaplace b / 32))
          ≤ (thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).im
            * (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).im := by
        have h1 : |(thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).im
            * (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).im|
            ≤ (Real.log b + 3) * xiRayLaplace b / 32 * (xiRayLaplace b / 32) := by
          rw [abs_mul]
          apply mul_le_mul himN himZ (abs_nonneg _) _
          positivity
        have := abs_le.mp h1
        linarith [this.1]
      nlinarith [hprod1, hprod2]
    have hden_pos : 0 < Complex.normSq (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)) := by
      nlinarith [hnsq_lo, hZ]
    have hnum0 : 0 ≤ (92 * Real.log b - 96) / 1024 * xiRayLaplace b ^ 2 := by
      apply mul_nonneg _ (sq_nonneg _)
      linarith
    have hstep1 : (92 * Real.log b - 96) / 1024 * xiRayLaplace b ^ 2
          / (1090 / 1024 * xiRayLaplace b ^ 2)
        ≤ ((thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).re
            * (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).re
          + (thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)).im
            * (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)).im)
          / Complex.normSq (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)) := by
      calc (92 * Real.log b - 96) / 1024 * xiRayLaplace b ^ 2
            / (1090 / 1024 * xiRayLaplace b ^ 2)
          ≤ (92 * Real.log b - 96) / 1024 * xiRayLaplace b ^ 2
              / Complex.normSq (thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)) :=
            div_le_div_of_nonneg_left hnum0 hden_pos hnsq_hi
        _ ≤ _ := div_le_div_of_nonneg_right hnum hden_pos.le
    have hval : (92 * Real.log b - 96) / 1024 * xiRayLaplace b ^ 2
        / (1090 / 1024 * xiRayLaplace b ^ 2) = (92 * Real.log b - 96) / 1090 := by
      rw [div_eq_div_iff (a := (92 * Real.log b - 96) / 1024 * xiRayLaplace b ^ 2)
        (ne_of_gt (by positivity)) (by norm_num : (1090 : ℝ) ≠ 0)]
      ring
    rw [hval] at hstep1
    have hfinal : Real.log b / 16 ≤ (92 * Real.log b - 96) / 1090 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith
    linarith
  · -- norm upper bound
    rw [hLid, norm_div]
    have hZcnorm : 31 / 32 * xiRayLaplace b
        ≤ ‖thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)‖ :=
      le_trans hreZlo (Complex.re_le_norm _)
    have hZcnorm0 : (0 : ℝ) < 31 / 32 * xiRayLaplace b := by positivity
    calc ‖thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖thetaBilateralLaplace ((b : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ‖thetaBilateralLaplaceMoment ((b : ℂ) + (t : ℂ) * Complex.I)‖
            / (31 / 32 * xiRayLaplace b) :=
          div_le_div_of_nonneg_left (norm_nonneg _) hZcnorm0 hZcnorm
      _ ≤ ((Real.log b + 3) * xiRayLaplace b) / (31 / 32 * xiRayLaplace b) :=
          div_le_div_of_nonneg_right hNc_norm hZcnorm0.le
      _ = 32 / 31 * (Real.log b + 3) := by
          rw [div_eq_iff (ne_of_gt hZcnorm0)]
          ring
      _ ≤ 4 * Real.log b := by linarith

/-- Inside the tilt budget the centered Xi logarithmic derivative keeps a logarithmic
real-part floor off the real ray. -/
theorem re_logDeriv_xiCent_tilted_ge {b t : ℝ} (hb : xiRayPacketBase ≤ b)
    (ht : |t| ≤ xiRayTiltBudget b) :
    Real.log b / 16 ≤ (logDeriv xiCent ((b : ℂ) + (t : ℂ) * Complex.I)).re :=
  (logDeriv_tilted_re_norm hb ht).1

/-- Inside the tilt budget the centered Xi logarithmic derivative keeps a logarithmic
norm ceiling off the real ray. -/
theorem norm_logDeriv_xiCent_tilted_le {b t : ℝ} (hb : xiRayPacketBase ≤ b)
    (ht : |t| ≤ xiRayTiltBudget b) :
    ‖logDeriv xiCent ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4 * Real.log b :=
  (logDeriv_tilted_re_norm hb ht).2

end RHTower

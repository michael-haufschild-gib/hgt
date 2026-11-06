import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNextAliasingCoefficientIsNegative
import GaloisForLFunctions.HTGeometry.SoninCosineRiemannLebesgue

/-!
# Weak averaging of the tilted-spline aliasing

The inverse-eighth-power aliasing converges against every integrable weight
supported away from zero. Summable harmonic bounds retain this limit for
weights converging in L¹.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open ArithmeticDegenerationTheory SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem tendsto_integrable_cos_average {F : ℝ → ℝ} (hF : Integrable F)
    {j : ℝ} (hj : 0 < j) :
    Tendsto (fun t : ℝ => ∫ x, F x * Real.cos (j * t * x)) atTop (𝓝 0) := by
  have h := (RHTower.tendsto_integral_mul_cos_atTop hF).comp
    ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).atTop_mul_const
      (div_pos hj (by positivity : 0 < 2 * Real.pi)))
  refine h.congr fun t => integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  congr 2
  dsimp only [Function.comp_def, id_eq]
  field_simp

/-- The periodic spline numerator has its mean against every integrable weight. -/
theorem tendsto_integrable_splineNumerator_average {F : ℝ → ℝ} (hF : Integrable F) :
    Tendsto (fun t : ℝ => ∫ x, F x * splineNumerator (t * x)) atTop
      (𝓝 (splineNumeratorMean * ∫ x, F x)) := by
  let a := Real.sinh 1 ^ 2 + 1 / 2
  have iF : Integrable F := hF
  have iC (t j : ℝ) : Integrable fun x => F x * Real.cos (j * t * x) :=
    RHTower.integrable_mul_cos hF (j * t)
  have hsplit (t : ℝ) : (∫ x, F x * splineNumerator (t * x)) -
      splineNumeratorMean * ∫ x, F x =
      (-2 * a ^ 3 - 3 * a / 8) * (∫ x, F x * Real.cos (2 * t * x)) +
      (3 * a ^ 2 / 4 + 1 / 32) * (∫ x, F x * Real.cos (4 * t * x)) -
      a / 8 * (∫ x, F x * Real.cos (6 * t * x)) +
      1 / 128 * (∫ x, F x * Real.cos (8 * t * x)) := by
    have heq : (fun x => F x * splineNumerator (t * x)) = fun x =>
        splineNumeratorMean * F x +
        (-2 * a ^ 3 - 3 * a / 8) * (F x * Real.cos (2 * t * x)) +
        (3 * a ^ 2 / 4 + 1 / 32) * (F x * Real.cos (4 * t * x)) -
        a / 8 * (F x * Real.cos (6 * t * x)) +
        1 / 128 * (F x * Real.cos (8 * t * x)) := by
      funext x
      rw [splineNumerator_cosine_expansion, splineNumeratorMean_eq]
      simp only [mul_assoc]
      dsimp only [a]
      ring
    have i0 : Integrable (fun x => splineNumeratorMean * F x) := iF.const_mul _
    have i2 : Integrable (fun x => (-2 * a ^ 3 - 3 * a / 8) *
        (F x * Real.cos (2 * t * x))) := (iC t 2).const_mul _
    have i4 : Integrable (fun x => (3 * a ^ 2 / 4 + 1 / 32) *
        (F x * Real.cos (4 * t * x))) := (iC t 4).const_mul _
    have i6 : Integrable (fun x => (a / 8) *
        (F x * Real.cos (6 * t * x))) := (iC t 6).const_mul _
    have i8 : Integrable (fun x => (1 / 128 : ℝ) *
        (F x * Real.cos (8 * t * x))) := (iC t 8).const_mul _
    have hs8 := integral_add (((i0.add i2).add i4).sub i6) i8
    have hs6 := integral_sub ((i0.add i2).add i4) i6
    have hs4 := integral_add (i0.add i2) i4
    have hs2 := integral_add i0 i2
    simp only [Pi.add_apply, Pi.sub_apply] at hs8 hs6 hs4 hs2
    rw [heq, hs8, hs6, hs4, hs2]
    simp only [integral_const_mul]
    ring
  have h2 := tendsto_integrable_cos_average hF (j := 2) (by norm_num)
  have h4 := tendsto_integrable_cos_average hF (j := 4) (by norm_num)
  have h6 := tendsto_integrable_cos_average hF (j := 6) (by norm_num)
  have h8 := tendsto_integrable_cos_average hF (j := 8) (by norm_num)
  have hlim := (((h2.const_mul (-2 * a ^ 3 - 3 * a / 8)).add
    (h4.const_mul (3 * a ^ 2 / 4 + 1 / 32))).sub (h6.const_mul (a / 8))).add
    (h8.const_mul (1 / 128))
  simp only [mul_zero, add_zero, sub_zero] at hlim
  have hd : Tendsto (fun t : ℝ => (∫ x, F x * splineNumerator (t * x)) -
      splineNumeratorMean * ∫ x, F x) atTop (𝓝 0) :=
    hlim.congr fun t => (hsplit t).symm
  simpa only [sub_add_cancel, zero_add] using
    hd.add_const (splineNumeratorMean * ∫ x, F x)

private theorem norm_supported_mul_le {F g : ℝ → ℝ} {δ C : ℝ}
    (hs : ∀ x, x < δ → F x = 0) (_hC : 0 ≤ C)
    (hg : ∀ x, δ ≤ x → ‖g x‖ ≤ C) (x : ℝ) :
    ‖F x * g x‖ ≤ C * ‖F x‖ := by
  by_cases hx : δ ≤ x
  · rw [norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hg x hx) (norm_nonneg _)
  · rw [hs x (lt_of_not_ge hx), zero_mul, norm_zero, mul_zero]

private theorem integrable_supported_mul {F g : ℝ → ℝ} {δ C : ℝ}
    (hF : Integrable F) (hs : ∀ x, x < δ → F x = 0)
    (hC : 0 ≤ C) (hg : AEStronglyMeasurable g volume)
    (hb : ∀ x, δ ≤ x → ‖g x‖ ≤ C) : Integrable (fun x => F x * g x) :=
  (hF.norm.const_mul C).mono' (hF.aestronglyMeasurable.mul hg)
    (Filter.Eventually.of_forall (norm_supported_mul_le hs hC hb))

private theorem integral_norm_supported_mul_le {F g : ℝ → ℝ} {δ C : ℝ}
    (hF : Integrable F) (hs : ∀ x, x < δ → F x = 0)
    (hC : 0 ≤ C) (hg : AEStronglyMeasurable g volume)
    (hb : ∀ x, δ ≤ x → ‖g x‖ ≤ C) :
    (∫ x, ‖F x * g x‖) ≤ C * ∫ x, ‖F x‖ := by
  have hi := integrable_supported_mul hF hs hC hg hb
  simpa only [integral_const_mul] using integral_mono_ae hi.norm
    (hF.norm.const_mul C) (Filter.Eventually.of_forall (norm_supported_mul_le hs hC hb))

private theorem inv_pow_le_of_le {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) (p : ℕ) :
    ‖(x ^ p)⁻¹‖ ≤ (δ ^ p)⁻¹ := by
  have hx0 : 0 < x := hδ.trans_le hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_anti₀ (pow_pos hδ p) (pow_le_pow_left₀ hδ.le hx p)

private theorem integrable_supported_inv_pow {F : ℝ → ℝ} {δ : ℝ}
    (hF : Integrable F) (hδ : 0 < δ) (hs : ∀ x, x < δ → F x = 0) (p : ℕ) :
    Integrable (fun x => F x * (x ^ p)⁻¹) :=
  integrable_supported_mul hF hs (by positivity)
    ((measurable_id.pow_const p).inv.aestronglyMeasurable)
    (fun _ hx => inv_pow_le_of_le hδ hx p)

private def aliasHarmonicBound (k : ℕ) : ℝ :=
  1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹

private theorem aliasHarmonicBound_nonneg (k : ℕ) : 0 ≤ aliasHarmonicBound k := by
  unfold aliasHarmonicBound
  positivity

private theorem summable_aliasHarmonicBound : Summable aliasHarmonicBound := by
  have h8 := (summable_nat_add_iff 1).mpr
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 8))
  exact (h8.congr fun k => by push_cast; rfl).mul_left _

private theorem continuous_tilted_spectrum : Continuous (shellSpectrum tiltedUnitSpline) :=
  continuous_shellSpectrum contDiff_tiltedUnitSpline.continuous
    (HasCompactSupport.intro isCompact_Icc fun x hx => tiltedUnitSpline_support x hx)

private theorem norm_scaled_harmonic_le {δ c x : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) (hx : δ ≤ x) (k : ℕ) :
    ‖c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x))‖ ≤
      aliasHarmonicBound k * (δ ^ 8)⁻¹ := by
  have hx0 := hδ.trans_le hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hc.le 8)
    (RenormalizedArithmeticPotentialTheory.CompletedShell.shellSpectrum_nonneg _))]
  refine (harmonic_le hc hx0 k).trans ?_
  exact mul_le_mul_of_nonneg_left
    (inv_anti₀ (pow_pos hδ 8) (pow_le_pow_left₀ hδ.le hx 8))
    (aliasHarmonicBound_nonneg k)

private theorem integrable_scaled_harmonic {F : ℝ → ℝ} {δ c : ℝ}
    (hF : Integrable F) (hδ : 0 < δ) (hs : ∀ x, x < δ → F x = 0)
    (hc : 0 < c) (k : ℕ) :
    Integrable fun x => F x * (c ^ 8 *
      shellSpectrum tiltedUnitSpline ((k + 1) * (c * x))) :=
  integrable_supported_mul hF hs
    (mul_nonneg (aliasHarmonicBound_nonneg k) (by positivity))
    ((continuous_const.mul (continuous_tilted_spectrum.comp (by fun_prop))).aestronglyMeasurable)
    (fun _ hx => norm_scaled_harmonic_le hδ hc hx k)

private theorem integral_norm_scaled_harmonic_le {F : ℝ → ℝ} {δ c : ℝ}
    (hF : Integrable F) (hδ : 0 < δ) (hs : ∀ x, x < δ → F x = 0)
    (hc : 0 < c) (k : ℕ) :
    (∫ x, ‖F x * (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x)))‖) ≤
      aliasHarmonicBound k * (δ ^ 8)⁻¹ * ∫ x, ‖F x‖ :=
  integral_norm_supported_mul_le hF hs
    (mul_nonneg (aliasHarmonicBound_nonneg k) (by positivity))
    ((continuous_const.mul (continuous_tilted_spectrum.comp (by fun_prop))).aestronglyMeasurable)
    (fun _ hx => norm_scaled_harmonic_le hδ hc hx k)

private theorem integrable_mul_splineNumerator {F : ℝ → ℝ} (hF : Integrable F) (t : ℝ) :
    Integrable fun x => F x * splineNumerator (t * x) := by
  apply hF.mul_bdd (c := (Real.sinh 1 ^ 2 + 1) ^ 4) ((continuous_splineNumerator.comp
    (continuous_const.mul continuous_id)).aestronglyMeasurable)
  filter_upwards with x
  change ‖splineNumerator (t * x)‖ ≤ (Real.sinh 1 ^ 2 + 1) ^ 4
  simpa only [Real.norm_eq_abs, abs_of_nonneg (splineNumerator_nonneg _)] using
    splineNumerator_le (t * x)

/-- Each harmonic has the inverse-eighth-power mean for an integrable weight. -/
private theorem tendsto_integrable_harmonic {F : ℝ → ℝ} {δ : ℝ}
    (hF : Integrable F) (hδ : 0 < δ) (hs : ∀ x, x < δ → F x = 0) (k : ℕ) :
    Tendsto (fun c : ℝ => ∫ x, F x *
      (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x)))) atTop
      (𝓝 (1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ *
        (splineNumeratorMean * ∫ x, F x * (x ^ 8)⁻¹))) := by
  let C : ℝ := 1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹
  let D : ℝ := 1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * 4 *
    (4 / Real.pi) ^ 10 * (δ ^ 10)⁻¹
  let r : ℝ := Real.pi * (k + 1) / 4
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  have iF8 := integrable_supported_inv_pow hF hδ hs 8
  have hmain := ((tendsto_integrable_splineNumerator_average iF8).comp
    ((tendsto_id : Tendsto (fun c : ℝ => c) atTop atTop).const_mul_atTop hr)).const_mul C
  have hbound (c : ℝ) (hc : 0 < c) (x : ℝ) (hx : δ ≤ x) :
      ‖c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x)) -
        C * ((x ^ 8)⁻¹ * splineNumerator (r * c * x))‖ ≤ D * (c ^ 2)⁻¹ := by
    have hb := abs_harmonic_sub_le hc (hδ.trans_le hx) k (H2 := 1) zero_le_one
    simp only [one_mul, mul_one] at hb
    have he : Real.pi * (k + 1) * c / 4 * x = r * c * x := by dsimp only [r]; ring
    rw [he] at hb
    rw [Real.norm_eq_abs]
    refine hb.trans ?_
    have hi := inv_anti₀ (pow_pos hδ 10) (pow_le_pow_left₀ hδ.le hx 10)
    calc _ ≤ 1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * 4 * (4 / Real.pi) ^ 10 *
          (c ^ 2)⁻¹ * (δ ^ 10)⁻¹ := by gcongr
      _ = D * (c ^ 2)⁻¹ := by dsimp only [D]; ring
  have herror : Tendsto (fun c : ℝ =>
      (∫ x, F x * (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x)))) -
      C * (∫ x, (F x * (x ^ 8)⁻¹) * splineNumerator (r * c * x))) atTop (𝓝 0) := by
    have hzero : Tendsto (fun c : ℝ => (D * (c ^ 2)⁻¹) * ∫ x, ‖F x‖) atTop (𝓝 0) := by
      have hpow : Tendsto (fun c : ℝ => c ^ 2) atTop atTop :=
        tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
      simpa only [mul_zero, zero_mul, Function.comp_def] using
        ((tendsto_inv_atTop_zero.comp hpow).const_mul D).mul_const (∫ x, ‖F x‖)
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    have ia := integrable_scaled_harmonic hF hδ hs hc k
    have ib := (integrable_mul_splineNumerator iF8 (r * c)).const_mul C
    have he : (∫ x, F x * (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x)))) -
        C * (∫ x, F x * (x ^ 8)⁻¹ * splineNumerator (r * c * x)) =
        ∫ x, F x * (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x)) -
          C * ((x ^ 8)⁻¹ * splineNumerator (r * c * x))) := by
      rw [← integral_const_mul, ← integral_sub ia ib]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [he]
    have hn := norm_integral_le_of_norm_le (hF.norm.const_mul (D * (c ^ 2)⁻¹))
      (Filter.Eventually.of_forall
        (norm_supported_mul_le hs (mul_nonneg hD (by positivity)) (hbound c hc)))
    simpa only [integral_const_mul] using hn
  have h := herror.add hmain
  simp only [zero_add, Function.comp_def, id_eq] at h
  exact h.congr fun c => sub_add_cancel _ _

private theorem summable_integral_norm_scaled_harmonic {F : ℝ → ℝ} {δ c : ℝ}
    (hF : Integrable F) (hδ : 0 < δ) (hs : ∀ x, x < δ → F x = 0) (hc : 0 < c) :
    Summable fun k : ℕ => ∫ x, ‖F x *
      (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x)))‖ :=
  ((summable_aliasHarmonicBound.mul_right (δ ^ 8)⁻¹).mul_right (∫ x, ‖F x‖)).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (integral_norm_scaled_harmonic_le hF hδ hs hc)

private theorem scaled_aliasIntegral_eq_tsum {F : ℝ → ℝ} {δ c : ℝ}
    (hF : Integrable F) (hδ : 0 < δ) (hs : ∀ x, x < δ → F x = 0) (hc : 0 < c) :
    (∫ x, F x * (c ^ 8 * aliasDensity tiltedUnitSpline (c * x))) =
      ∑' k : ℕ, ∫ x, F x * (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x))) := by
  rw [integral_tsum_of_summable_integral_norm (integrable_scaled_harmonic hF hδ hs hc)
    (summable_integral_norm_scaled_harmonic hF hδ hs hc)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [aliasDensity, tsum_mul_left]

/-- The actual tilted-spline aliasing has its Jordan mean against every L¹ weight
supported a positive distance from zero. -/
theorem tendsto_integrable_tilted_aliasDensity {F : ℝ → ℝ} {δ : ℝ}
    (hF : Integrable F) (hδ : 0 < δ) (hs : ∀ x, x < δ → F x = 0) :
    Tendsto (fun c : ℝ => ∫ x, F x * (c ^ 8 * aliasDensity tiltedUnitSpline (c * x)))
      atTop (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ x, F x * (x ^ 8)⁻¹)) := by
  have hsum := (summable_aliasHarmonicBound.mul_right (δ ^ 8)⁻¹).mul_right (∫ x, ‖F x‖)
  have hT := tendsto_tsum_of_dominated_convergence hsum
    (tendsto_integrable_harmonic hF hδ hs) (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      intro k
      exact (norm_integral_le_integral_norm _).trans
        (integral_norm_scaled_harmonic_le hF hδ hs hc k))
  have heq : (∑' k : ℕ, 1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ *
      (splineNumeratorMean * ∫ x, F x * (x ^ 8)⁻¹)) =
      (7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ x, F x * (x ^ 8)⁻¹ := by
    linarith only [aliasLimit_eq (∫ x, F x * (x ^ 8)⁻¹)]
  rw [heq] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  exact (scaled_aliasIntegral_eq_tsum hF hδ hs hc).symm

private theorem norm_scaled_aliasDensity_le {δ c x : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) (hx : δ ≤ x) :
    ‖c ^ 8 * aliasDensity tiltedUnitSpline (c * x)‖ ≤
      (∑' k, aliasHarmonicBound k) * (δ ^ 8)⁻¹ := by
  have hx0 : 0 < x := hδ.trans_le hx
  have hsum := (hasAlias_tilted (c * x) (mul_pos hc hx0)).mul_left (c ^ 8)
  have hb := summable_aliasHarmonicBound.mul_right (δ ^ 8)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg hc.le 8) (aliasDensity_nonneg _)), ← hsum.tsum_eq, ← tsum_mul_right]
  exact hsum.summable.tsum_le_tsum (fun k =>
    (le_abs_self _).trans (norm_scaled_harmonic_le hδ hc hx k)) hb

/-- The scaled aliasing acts with one L¹ bound, independent of the overlap. -/
theorem exists_integrable_tilted_aliasDensity_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ F : ℝ → ℝ, Integrable F →
      (∀ x, x < δ → F x = 0) → ∀ c : ℝ, 0 < c →
      ‖∫ x, F x * (c ^ 8 * aliasDensity tiltedUnitSpline (c * x))‖ ≤ B * ∫ x, ‖F x‖ := by
  let B : ℝ := (∑' k, aliasHarmonicBound k) * (δ ^ 8)⁻¹
  have hB : 0 ≤ B := mul_nonneg (tsum_nonneg aliasHarmonicBound_nonneg) (by positivity)
  refine ⟨B, hB, ?_⟩
  intro F hF hs c hc
  have hb := norm_integral_le_of_norm_le (hF.norm.const_mul B)
    (Filter.Eventually.of_forall
      (norm_supported_mul_le hs hB (fun _ hx => norm_scaled_aliasDensity_le hδ hc hx)))
  simpa only [integral_const_mul] using hb

private theorem scaled_aliasIntegral_sub {F G : ℝ → ℝ} {δ c : ℝ}
    (hF : Integrable F) (hG : Integrable G) (hδ : 0 < δ)
    (hsF : ∀ x, x < δ → F x = 0) (hsG : ∀ x, x < δ → G x = 0) (hc : 0 < c) :
    (∫ x, F x * (c ^ 8 * aliasDensity tiltedUnitSpline (c * x))) -
      (∫ x, G x * (c ^ 8 * aliasDensity tiltedUnitSpline (c * x))) =
      ∫ x, (F x - G x) * (c ^ 8 * aliasDensity tiltedUnitSpline (c * x)) := by
  have hsD : ∀ x, x < δ → F x - G x = 0 := by
    intro x hx
    rw [hsF x hx, hsG x hx, sub_self]
  have hFsum := (summable_integral_norm_scaled_harmonic hF hδ hsF hc).of_norm_bounded
    (fun k => norm_integral_le_integral_norm
      (fun x => F x * (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x)))))
  have hGsum := (summable_integral_norm_scaled_harmonic hG hδ hsG hc).of_norm_bounded
    (fun k => norm_integral_le_integral_norm
      (fun x => G x * (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x)))))
  have hiD : Integrable (fun x => F x - G x) := hF.sub hG
  rw [scaled_aliasIntegral_eq_tsum hF hδ hsF hc,
    scaled_aliasIntegral_eq_tsum hG hδ hsG hc,
    scaled_aliasIntegral_eq_tsum hiD hδ hsD hc, ← hFsum.tsum_sub hGsum]
  apply tsum_congr
  intro k
  rw [← integral_sub (integrable_scaled_harmonic hF hδ hsF hc k)
    (integrable_scaled_harmonic hG hδ hsG hc k)]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- Strong L¹ convergence of weights preserves the actual aliasing limit even
when the weight and overlap vary together. -/
theorem tendsto_tilted_aliasDensity_of_L1_convergence {ι : Type*} {l : Filter ι} {F : ℝ → ℝ}
    {Fₙ : ι → ℝ → ℝ} {δ : ℝ} (hF : Integrable F) (hFₙ : ∀ n, Integrable (Fₙ n))
    (hδ : 0 < δ) (hs : ∀ x, x < δ → F x = 0)
    (hsₙ : ∀ n x, x < δ → Fₙ n x = 0)
    (hL1 : Tendsto (fun n => ∫ x, ‖Fₙ n x - F x‖) l (𝓝 0))
    {c : ι → ℝ} (hc : Tendsto c l atTop) :
    Tendsto (fun n => ∫ x, Fₙ n x * (c n ^ 8 * aliasDensity tiltedUnitSpline (c n * x)))
      l (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ x, F x * (x ^ 8)⁻¹)) := by
  obtain ⟨B, hB, hbound⟩ := exists_integrable_tilted_aliasDensity_bound hδ
  have herror : Tendsto (fun n =>
      (∫ x, Fₙ n x * (c n ^ 8 * aliasDensity tiltedUnitSpline (c n * x))) -
      (∫ x, F x * (c n ^ 8 * aliasDensity tiltedUnitSpline (c n * x)))) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hL1.const_mul B)
    filter_upwards [hc.eventually_gt_atTop 0] with n hcn
    rw [scaled_aliasIntegral_sub (hFₙ n) hF hδ (hsₙ n) hs hcn]
    exact hbound (fun x => Fₙ n x - F x) ((hFₙ n).sub hF)
      (fun x hx => by rw [hsₙ n x hx, hs x hx, sub_self]) (c n) hcn
  have h := herror.add ((tendsto_integrable_tilted_aliasDensity hF hδ hs).comp hc)
  simp only [zero_add, Function.comp_def] at h
  exact h.congr fun n => sub_add_cancel _ _

#print axioms tendsto_integrable_tilted_aliasDensity
#print axioms tendsto_tilted_aliasDensity_of_L1_convergence

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

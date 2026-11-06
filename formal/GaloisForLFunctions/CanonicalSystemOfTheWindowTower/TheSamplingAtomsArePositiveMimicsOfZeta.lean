import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ThePrecontactWeilSpacesHaveSamplingBases
import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.ZetaTransfer
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniHilbertOne
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity

/-!
# The sampling atoms are positive on-line mimics of zeta

Below the onset, the de Branges sampling formula represents the Weil form of every smooth window
as a positive sum over real points. Placed on the critical line, the atoms `1 / K(t,t)` are a
positive on-line weighting with exactly the zeta image on the given aperture. So the existence of
such a mimic is equivalent to positivity of the window, and the sampling atoms obey the sharp local
weighted count, with constants uniform in the phase.

The Lorentzian mass of the atoms is finite because the tilted indicator `e^{-s} 1_{[0,b]}` is a
Weil vector: its transform decays exactly like `1/t` with no real near-zeros, while the form weight
grows only logarithmically.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

open _root_.RHTower Zeta23 ZeroConfigurationGeometry

variable (a : PrecontactAperture)

/-! ### A Weil vector with the Lorentzian rate -/

/-- The tilted indicator `e^{-s} 1_{[0,b]}`. -/
def tiltProfile (b : ℝ) : ℝ → ℂ := (Icc 0 b).indicator fun s => ((Real.exp (-s) : ℝ) : ℂ)

theorem memLp_tiltProfile (b : ℝ) : MemLp (tiltProfile b) 2 volume := by
  have hc : Continuous fun s : ℝ => ((Real.exp (-s) : ℝ) : ℂ) := by fun_prop
  have hmeas : AEStronglyMeasurable (tiltProfile b) volume :=
    hc.aestronglyMeasurable.indicator measurableSet_Icc
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have heq : (fun x => ‖tiltProfile b x‖ ^ 2) =
      (Icc 0 b).indicator (fun s => ‖((Real.exp (-s) : ℝ) : ℂ)‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ Icc 0 b
    · simp only [tiltProfile, indicator_of_mem hx]
    · simp only [tiltProfile, indicator_of_notMem hx, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
  rw [heq]
  exact (Continuous.integrableOn_Icc (by fun_prop)).integrable_indicator measurableSet_Icc

/-- The class of the tilted indicator, cut off to its aperture. -/
def tiltL2 (b : ℝ) : SoninL2 := suzukiCutoff b ((memLp_tiltProfile b).toLp _)

theorem tiltL2_ae {b : ℝ} (hb : 0 ≤ b) : (tiltL2 b : ℝ → ℂ) =ᵐ[volume] tiltProfile b := by
  filter_upwards [indicatorCutoff_ae (Icc (-b) b) measurableSet_Icc ((memLp_tiltProfile b).toLp _),
    (memLp_tiltProfile b).coeFn_toLp] with s h1 h2
  change (suzukiCutoff b ((memLp_tiltProfile b).toLp _) : ℝ → ℂ) s = _
  rw [h1]
  by_cases hs : s ∈ Icc (-b) b
  · rw [indicator_of_mem hs, h2]
  · rw [indicator_of_notMem hs]
    have hs' : s ∉ Icc 0 b := fun h => hs ⟨by linarith only [h.1, hb], h.2⟩
    simp only [tiltProfile, indicator_of_notMem hs']

theorem tiltL2_fixed (b : ℝ) : suzukiCutoff b (tiltL2 b) = tiltL2 b := by
  have hidem := indicatorCutoff_idempotent (Icc (-b) b) measurableSet_Icc
  rw [isIdempotentElem_iff] at hidem
  exact congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T ((memLp_tiltProfile b).toLp _)) hidem

theorem tilt_denominator_ne (t : ℝ) : I * (t : ℂ) - 1 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

/-- Closed form of the tilted transform on the real line. -/
theorem compactFourier_tiltL2 {b : ℝ} (hb : 0 ≤ b) (t : ℝ) :
    suzukiCompactL2Fourier b (tiltL2 b) (t : ℂ) =
      (Complex.exp ((I * t - 1) * b) - 1) / (I * t - 1) := by
  rw [suzukiCompactL2Fourier_eq_full_integral_of_fixed (tiltL2_fixed b)]
  have hae : (fun s : ℝ => Complex.exp (I * t * (s : ℂ)) * (tiltL2 b) s) =ᵐ[volume]
      (Icc 0 b).indicator fun s : ℝ => Complex.exp ((I * t - 1) * s) := by
    filter_upwards [tiltL2_ae hb] with s hs
    rw [hs]
    by_cases hm : s ∈ Icc 0 b
    · simp only [tiltProfile, indicator_of_mem hm]
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp only [tiltProfile, indicator_of_notMem hm, mul_zero]
  rw [integral_congr_ae hae, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb,
    integral_exp_mul_complex (tilt_denominator_ne t)]
  simp

theorem norm_exp_tilt (b t : ℝ) : ‖Complex.exp ((I * t - 1) * b)‖ = Real.exp (-b) := by
  rw [Complex.norm_exp]
  congr 1
  simp

theorem norm_sq_tilt_denominator (t : ℝ) : ‖I * (t : ℂ) - 1‖ ^ 2 = 1 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- Upper bound for the tilted transform. -/
theorem norm_sq_tiltTransform_le {b : ℝ} (hb : 0 ≤ b) (t : ℝ) :
    ‖suzukiCompactL2Fourier b (tiltL2 b) (t : ℂ)‖ ^ 2 ≤ 4 / (1 + t ^ 2) := by
  have hnum : ‖Complex.exp ((I * t - 1) * b) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_exp_tilt, norm_one]
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb)
    linarith only [this]
  rw [compactFourier_tiltL2 hb, norm_div, div_pow, norm_sq_tilt_denominator]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h0 := norm_nonneg (Complex.exp ((I * t - 1) * b) - 1)
  nlinarith only [hnum, h0]

/-- Lower bound for the tilted transform: there are no real near-zeros. -/
theorem le_norm_sq_tiltTransform {b : ℝ} (hb : 0 ≤ b) (t : ℝ) :
    (1 - Real.exp (-b)) ^ 2 / (1 + t ^ 2) ≤
      ‖suzukiCompactL2Fourier b (tiltL2 b) (t : ℂ)‖ ^ 2 := by
  have hnum : 1 - Real.exp (-b) ≤ ‖Complex.exp ((I * t - 1) * b) - 1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (Complex.exp ((I * t - 1) * b))
    rw [norm_one, norm_exp_tilt, norm_sub_rev] at h
    exact h
  rw [compactFourier_tiltL2 hb, norm_div, div_pow, norm_sq_tilt_denominator]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h0 : 0 ≤ 1 - Real.exp (-b) := by
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb)
    linarith only [this]
  exact pow_le_pow_left₀ h0 hnum 2

/-- The tilted indicator has finite form norm. -/
theorem memLp_fourierUnitary_tiltL2 {b : ℝ} (hb : 0 ≤ b) :
    MemLp (fun ξ : ℝ => (fourierUnitary (tiltL2 b) : ℝ → ℂ) ξ) 2 ccmArchimedeanFormMeasure := by
  have hae := fourierUnitary_ae_eq_compactFourier (tiltL2_fixed b)
  have hm0 : AEStronglyMeasurable (fun ξ : ℝ => (fourierUnitary (tiltL2 b) : ℝ → ℂ) ξ) volume :=
    Lp.aestronglyMeasurable _
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ => (fourierUnitary (tiltL2 b) : ℝ → ℂ) ξ)
      ccmArchimedeanFormMeasure :=
    hm0.mono_ac ccmArchimedeanFormMeasure_absolutelyContinuous_volume
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (integrable_withDensity_iff_integrable_smul
    measurable_ccmArchimedeanFormWeightNNReal).mpr ?_
  obtain ⟨C, hC, hω⟩ := exists_formWeight_le_sqrt
  have hmaj : Integrable fun ξ : ℝ => (8 * C) * (1 + ‖ξ‖) ^ (-(3 / 2 : ℝ)) :=
    (integrable_one_add_norm (by simp; norm_num)).const_mul _
  refine hmaj.mono' ?_ ?_
  · exact measurable_ccmArchimedeanFormWeightNNReal.aestronglyMeasurable.smul
      (hm0.norm.pow 2)
  filter_upwards [hae] with ξ hξ
  rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal, hξ, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (ccmArchimedeanFormWeight_pos ξ).le (sq_nonneg _)),
    Real.norm_eq_abs]
  have hup := norm_sq_tiltTransform_le hb (-(2 * Real.pi * ξ))
  set s : ℝ := 1 + |ξ| with hs
  have hs1 : 1 ≤ s := by
    rw [hs]
    linarith only [abs_nonneg ξ]
  have hs0 : 0 < s := by linarith only [hs1]
  have hq : s ^ 2 ≤ 2 * (1 + (-(2 * Real.pi * ξ)) ^ 2) := by
    have h1 : (-(2 * Real.pi * ξ)) ^ 2 = (2 * Real.pi) ^ 2 * |ξ| ^ 2 := by
      rw [neg_sq, mul_pow, sq_abs]
    have h2 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith only [Real.pi_gt_three]
    rw [h1, hs]
    nlinarith only [sq_nonneg (|ξ| - 1), sq_nonneg |ξ|, h2]
  have hrpow : s ^ (-(3 / 2 : ℝ)) = Real.sqrt s / s ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast s 2, ← Real.rpow_sub hs0]
    norm_num
  rw [hrpow]
  have hd : 0 < 1 + (-(2 * Real.pi * ξ)) ^ 2 := by positivity
  have h4 : 4 / (1 + (-(2 * Real.pi * ξ)) ^ 2) ≤ 8 / s ^ 2 := by
    rw [div_le_div_iff₀ hd (by positivity)]
    nlinarith only [hq]
  calc
    ccmArchimedeanFormWeight ξ *
        ‖suzukiCompactL2Fourier b (tiltL2 b) ((-(2 * Real.pi * ξ) : ℝ) : ℂ)‖ ^ 2 ≤
        (C * Real.sqrt s) * (8 / s ^ 2) :=
      mul_le_mul (hω ξ) (hup.trans h4) (sq_nonneg _) (by positivity)
    _ = 8 * C * (Real.sqrt s / s ^ 2) := by ring

/-- A Weil vector whose transform is bounded below by the Lorentzian rate on the whole line. -/
theorem exists_lorentzian_vector :
    ∃ y : WeilHilbertBeforeContact a, ∃ c : ℝ, 0 < c ∧
      ∀ t : ℝ, c / (1 + t ^ 2) ≤ ‖fourier a y (t : ℂ)‖ ^ 2 := by
  have hb : 0 < a.1.1 := a.1.2
  let f : suzukiApertureHilbert a.1 := ⟨tiltL2 a.1.1, ⟨(memLp_tiltProfile a.1.1).toLp _, rfl⟩⟩
  obtain ⟨u, hu⟩ := exists_ccmArchimedeanFormDomain_of_fourier_memLp a.1 f
    (memLp_fourierUnitary_tiltL2 hb.le)
  refine ⟨(toForm a).symm u, (1 - Real.exp (-a.1.1)) ^ 2, ?_, fun t => ?_⟩
  · have : Real.exp (-a.1.1) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr hb)
    exact pow_pos (by linarith only [this]) 2
  · have hF : fourier a ((toForm a).symm u) (t : ℂ) =
        suzukiCompactL2Fourier a.1.1 (tiltL2 a.1.1) (t : ℂ) := by
      rw [fourier_eq_whole, LinearEquiv.apply_symm_apply, hu]
    rw [hF]
    exact le_norm_sq_tiltTransform hb.le t

/-! ### Smooth windows as Weil vectors -/

/-- A smooth window of aperture `r < a` as a smooth interior source. -/
def windowSource {r : ℝ} (hr : r < a.1.1) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : tsupport f ⊆ Icc (-r) r) : CCMComplexSmoothInteriorSource a.1 where
  toFun := f
  smooth := hf
  hasCompactSupport := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hs
  tsupport_subset := hs.trans (Icc_subset_Ioo (neg_lt_neg hr) hr)

/-- A smooth window of aperture `r < a` as a Weil vector. -/
def windowVector {r : ℝ} (hr : r < a.1.1) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : tsupport f ⊆ Icc (-r) r) : WeilHilbertBeforeContact a :=
  smoothCore a (ccmComplexSmoothInteriorSourceToSuzukiTaSmoothCore a.1 (windowSource a hr hf hs))

theorem fourier_windowVector {r : ℝ} (hr : r < a.1.1) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : tsupport f ⊆ Icc (-r) r) (z : ℂ) :
    fourier a (windowVector a hr hf hs) z = paperFT f z := by
  change eval a z (smoothCore a _) = _
  rw [eval_smoothCore_eq_integral, paperFT]
  apply integral_congr_ae
  filter_upwards with x
  exact mul_comm _ _

theorem inner_windowVector {r : ℝ} (hr : r < a.1.1) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : tsupport f ⊆ Icc (-r) r) :
    inner ℂ (windowVector a hr hf hs) (windowVector a hr hf hs) = zetaZeroConfig.W f f := by
  rw [inner_eq_weil, windowVector, toForm_smoothCore]
  exact ccmRestrictedWeilForm_complexSmooth_eq_zetaWeil
    (suzukiTaSmoothCoreToSource a.1 _) (suzukiTaSmoothCoreToSource a.1 _)

/-! ### The sampling atoms on the critical line -/

/-- The point of the critical line at height `t`. -/
def criticalPoint (t : ℝ) : ℂ := 1 / 2 + t * I

@[simp] theorem criticalPoint_re (t : ℝ) : (criticalPoint t).re = 1 / 2 := by
  simp [criticalPoint]

@[simp] theorem criticalPoint_im (t : ℝ) : (criticalPoint t).im = t := by
  simp [criticalPoint]

theorem criticalPoint_injective : Function.Injective criticalPoint := fun s t h => by
  simpa using congrArg Complex.im h

theorem gammaOf_criticalPoint (t : ℝ) : gammaOf (criticalPoint t) = (t : ℂ) := by
  apply Complex.ext
  · rw [gammaOf_re_eq_im, Complex.ofReal_re, criticalPoint_im]
  · rw [gammaOf_im_eq, criticalPoint_re, sub_self, Complex.ofReal_im]

/-- The sampling atoms `1 / K(t,t)` placed on the critical line. -/
def samplingWeight (φ z : ℂ) : ℝ :=
  open Classical in
  if z.re = 1 / 2 ∧ z.im ∈ samplingSet a φ then (‖evalVector a (z.im : ℂ)‖ ^ 2)⁻¹ else 0

theorem samplingWeight_criticalPoint {φ : ℂ} (t : samplingSet a φ) :
    samplingWeight a φ (criticalPoint (t : ℝ)) = (‖evalVector a ((t : ℝ) : ℂ)‖ ^ 2)⁻¹ := by
  rw [samplingWeight, if_pos ⟨criticalPoint_re _, by simp⟩, criticalPoint_im]

theorem samplingWeight_nonneg (φ z : ℂ) : 0 ≤ samplingWeight a φ z := by
  rw [samplingWeight]
  split_ifs <;> positivity

theorem samplingWeight_onLine {φ z : ℂ} (h : samplingWeight a φ z ≠ 0) : z.re = 1 / 2 := by
  by_contra hne
  apply h
  rw [samplingWeight, if_neg fun hc => hne hc.1]

/-- The embedding of the sampling set in the critical line. -/
def samplingEmbedding (φ : ℂ) : samplingSet a φ → ℂ := fun t => criticalPoint (t : ℝ)

theorem samplingEmbedding_injective (φ : ℂ) : Function.Injective (samplingEmbedding a φ) :=
  fun _ _ h => Subtype.ext (criticalPoint_injective h)

theorem samplingWeight_eq_zero_off {φ z : ℂ} (hz : z ∉ Set.range (samplingEmbedding a φ)) :
    samplingWeight a φ z = 0 := by
  rw [samplingWeight, if_neg]
  rintro ⟨hre, him⟩
  apply hz
  refine ⟨⟨z.im, him⟩, ?_⟩
  apply Complex.ext
  · change (criticalPoint z.im).re = _
    rw [criticalPoint_re, hre]
  · change (criticalPoint z.im).im = _
    rw [criticalPoint_im]

/-- The Lorentzian mass of the sampling atoms is finite. -/
theorem summable_samplingWeight {φ : ℂ} (hφ : ‖φ‖ = 1) (hE : ¬ IsExceptionalPhase a φ) :
    Summable fun z => |samplingWeight a φ z| / (1 + Complex.normSq (gammaOf z)) := by
  obtain ⟨y, c, hc, hy⟩ := exists_lorentzian_vector a
  have hS := (hasSum_norm_sq_sampling a hφ hE y).summable
  rw [← (samplingEmbedding_injective a φ).summable_iff]
  · refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_) (hS.mul_left c⁻¹)
    · exact div_nonneg (abs_nonneg _) (add_nonneg zero_le_one (Complex.normSq_nonneg _))
    · simp only [Function.comp_apply, samplingEmbedding]
      rw [samplingWeight_criticalPoint, gammaOf_criticalPoint, Complex.normSq_ofReal,
        abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖evalVector a ((t : ℝ) : ℂ)‖))]
      have hb := hy (t : ℝ)
      have hpos : 0 < 1 + ((t : ℝ) : ℝ) * (t : ℝ) := by nlinarith only [mul_self_nonneg (t : ℝ)]
      have hb' : c / (1 + (t : ℝ) * (t : ℝ)) ≤ ‖fourier a y (((t : ℝ) : ℝ) : ℂ)‖ ^ 2 := by
        rw [← sq]
        exact hb
      have hk : 0 ≤ (‖evalVector a ((t : ℝ) : ℂ)‖ ^ 2)⁻¹ := by positivity
      have hdiv : (1 + (t : ℝ) * (t : ℝ))⁻¹ ≤ c⁻¹ * ‖fourier a y (((t : ℝ) : ℝ) : ℂ)‖ ^ 2 := by
        rw [inv_mul_eq_div, le_div_iff₀ hc]
        rw [div_eq_mul_inv] at hb'
        linarith only [hb']
      rw [div_eq_mul_inv]
      calc
        (‖evalVector a ((t : ℝ) : ℂ)‖ ^ 2)⁻¹ * (1 + (t : ℝ) * (t : ℝ))⁻¹ ≤
            (‖evalVector a ((t : ℝ) : ℂ)‖ ^ 2)⁻¹ *
              (c⁻¹ * ‖fourier a y (((t : ℝ) : ℝ) : ℂ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hdiv hk
        _ = _ := by ring
  · intro z hz
    rw [samplingWeight_eq_zero_off a hz, abs_zero, zero_div]

/-- The sampling atoms reproduce the zeta image on every smooth window inside the aperture. -/
theorem weightedImage_samplingWeight {φ : ℂ} (hφ : ‖φ‖ = 1) (hE : ¬ IsExceptionalPhase a φ)
    {r : ℝ} (hr : r < a.1.1) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : tsupport f ⊆ Icc (-r) r) :
    weightedImage (fun z => (samplingWeight a φ z : ℂ)) f f = zetaZeroConfig.W f f := by
  have hS := hasSum_sampling a hφ hE (windowVector a hr hf hs) (windowVector a hr hf hs)
  rw [inner_windowVector] at hS
  have hmain : HasSum (fun z => (samplingWeight a φ z : ℂ) * pointImage f f z)
      (zetaZeroConfig.W f f) := by
    rw [← (samplingEmbedding_injective a φ).hasSum_iff]
    · have hfun : (fun z => (samplingWeight a φ z : ℂ) * pointImage f f z) ∘
          samplingEmbedding a φ = fun t : samplingSet a φ =>
            ((‖evalVector a ((t : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
              (conj (fourier a (windowVector a hr hf hs) ((t : ℝ) : ℂ)) *
                fourier a (windowVector a hr hf hs) ((t : ℝ) : ℂ)) := by
        funext t
        simp only [Function.comp_apply, samplingEmbedding]
        rw [samplingWeight_criticalPoint, pointImage, gammaOf_criticalPoint, Complex.conj_ofReal,
          fourier_windowVector]
        push_cast
        ring
      rw [hfun]
      exact hS
    · intro z hz
      rw [samplingWeight_eq_zero_off a hz, Complex.ofReal_zero, zero_mul]
  exact hmain.tsum_eq

/-- **The sampling atoms obey the sharp local weighted count.** Constants depend on the aperture
and the density slack only, not on the phase. -/
theorem samplingAtoms_weighted_count {θ : ℝ} (hθ : 1 < θ) :
    ∃ A T₀ : ℝ, 0 ≤ A ∧ 40 ≤ T₀ ∧ ∀ φ : ℂ, ‖φ‖ = 1 → ¬ IsExceptionalPhase a φ →
      ∀ T : ℝ, T₀ ≤ T → ∀ x y : ℝ, x ≤ y → ∀ s : Finset ℝ,
      (∀ t ∈ s, t ∈ samplingSet a φ ∧ |t - T| ≤ T / 2 ∧ t ∈ Icc x y) →
        (∑ t ∈ s, (‖evalVector a (t : ℂ)‖ ^ 2)⁻¹) ≤
          θ / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) * (y - x) +
            A * Real.log (T / (2 * Real.pi)) := by
  classical
  have hb : 0 < a.1.1 := a.1.2
  have hr : a.1.1 / 2 < a.1.1 := by linarith only [hb]
  obtain ⟨A, T₀, hA, hT₀, hcount⟩ :=
    zeta_positive_mimic_weighted_count_of_smooth (half_pos hb) hθ
  refine ⟨A, T₀, hA, hT₀, fun φ hφ hE T hT x y hxy s hs => ?_⟩
  have h := hcount (samplingWeight a φ) (samplingWeight_nonneg a φ)
    (fun z hz => samplingWeight_onLine a hz) (summable_samplingWeight a hφ hE)
    (fun f hf hsupp => weightedImage_samplingWeight a hφ hE hr hf hsupp) T hT x y hxy
    (s.map ⟨criticalPoint, criticalPoint_injective⟩) (by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hz
      simpa only [Function.Embedding.coeFn_mk, criticalPoint_im] using (hs t ht).2)
  rw [Finset.sum_map] at h
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro t ht
  exact (samplingWeight_criticalPoint a (φ := φ) ⟨t, (hs t ht).1⟩).symm

/-- Below the onset every aperture carries a positive on-line mimic of the zeta image. -/
theorem exists_positive_mimic_of_lt_onset {r : ℝ}
    (hr : (r : EReal) < WindowVisibilityLaw.onsetAperture zetaZeroConfig) (hr0 : 0 < r) :
    ∃ w : ℂ → ℝ, (∀ z, 0 ≤ w z) ∧ (∀ z, w z ≠ 0 → z.re = 1 / 2) ∧
      (Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z))) ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → tsupport f ⊆ Icc (-r) r →
        weightedImage (fun z => (w z : ℂ)) f f = zetaZeroConfig.W f f := by
  obtain ⟨b, hrb, hb⟩ := EReal.lt_iff_exists_real_btwn.mp hr
  have hrb' : r < b := EReal.coe_lt_coe_iff.mp hrb
  let c : PrecontactAperture := ⟨⟨b, hr0.trans hrb'⟩, hb⟩
  obtain ⟨φ, hφ, hE⟩ := exists_not_isExceptionalPhase c
  exact ⟨samplingWeight c φ, samplingWeight_nonneg c φ,
    fun z hz => samplingWeight_onLine c hz, summable_samplingWeight c hφ hE,
    fun f hf hs => weightedImage_samplingWeight c hφ hE hrb' hf hs⟩

/-- A positive on-line mimic of the zeta image forces positivity of the window. -/
theorem re_W_nonneg_of_positive_mimic {w : ℂ → ℝ} {r : ℝ} (hw0 : ∀ z, 0 ≤ w z)
    (hline : ∀ z, w z ≠ 0 → z.re = 1 / 2)
    (hw : Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z)))
    (himage : ∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → tsupport f ⊆ Icc (-r) r →
      weightedImage (fun z => (w z : ℂ)) f f = zetaZeroConfig.W f f)
    {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : tsupport f ⊆ Icc (-r) r) :
    0 ≤ (zetaZeroConfig.W f f).re := by
  rw [← himage f hf hs,
    (weightedImage_onLine_diagonal hline hw (hf.of_le (by norm_cast))
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hs)).2]
  exact tsum_nonneg fun z => mul_nonneg (hw0 z) (sq_nonneg _)

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact.exists_lorentzian_vector
#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact.summable_samplingWeight
#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact.weightedImage_samplingWeight
#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact.samplingAtoms_weighted_count
#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact.exists_positive_mimic_of_lt_onset
#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact.re_W_nonneg_of_positive_mimic

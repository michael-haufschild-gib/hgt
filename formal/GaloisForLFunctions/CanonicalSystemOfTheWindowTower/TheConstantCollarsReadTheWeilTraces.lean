import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilCollarResidualsHaveTheirActualL2Limit
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheFullWeilFormControlsBothCollars

/-!
# Constant collar tests read the actual Weil endpoint traces

Strong convergence of the rescaled residual gives the normalized average
against the constant collar. This is the linear readout needed in the
variational lower bound for the moving-window kernel.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
open ArithmeticContinuationAndCriticalEnergy

private theorem dilation_intervalSource {h : ℝ} (hh : 0 < h) :
    dilation h hh (logarithmicIntervalSource 0 h) =
      (Real.sqrt h : ℂ) • logarithmicIntervalSource 0 1 := by
  apply Lp.ext
  have hc := (logarithmicIntervalSource_coeFn 0 h).comp_tendsto
    (realMul_quasiMeasurePreserving h hh.ne').tendsto_ae
  filter_upwards [dilation_ae h hh (logarithmicIntervalSource 0 h), hc,
    Lp.coeFn_smul (Real.sqrt h : ℂ) (logarithmicIntervalSource 0 1),
    logarithmicIntervalSource_coeFn 0 1] with s hd hc hm hu
  change logarithmicIntervalSource 0 h (h*s) =
    (Ioc (0 : ℝ) h).indicator (fun _ => (1 : ℂ)) (h*s) at hc
  rw [hd, hc, hm, Pi.smul_apply, smul_eq_mul, hu]
  have he : h*s ∈ Ioc (0 : ℝ) h ↔ s ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · intro hs
      exact ⟨(mul_pos_iff_of_pos_left hh).mp hs.1,
        (mul_le_mul_iff_right₀ hh).mp (by simpa only [mul_one, mul_comm] using hs.2)⟩
    · intro hs
      exact ⟨mul_pos hh hs.1, mul_le_of_le_one_right hh.le hs.2⟩
  simp only [indicator_apply, he]

private theorem unit_intervalSource_cut :
    indicatorCutoff (Ioc (0 : ℝ) 1) measurableSet_Ioc (logarithmicIntervalSource 0 1) =
      logarithmicIntervalSource 0 1 := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Ioc (0 : ℝ) 1) measurableSet_Ioc
    (logarithmicIntervalSource 0 1), logarithmicIntervalSource_coeFn 0 1] with s hc hu
  rw [hc, hu]
  by_cases hs : s ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hs]
  · rw [indicator_of_notMem hs, indicator_of_notMem hs]

/-- The rescaled unit-interval pairing is the literal collar mean divided by
`h sqrt(log(1/h))`. -/
theorem inner_intervalSource_logarithmicCollarRescaling {h : ℝ} (hh : 0 < h)
    (f : SoninL2) :
    inner ℂ (logarithmicIntervalSource 0 1) (logarithmicCollarRescaling h f) =
      inner ℂ (logarithmicIntervalSource 0 h) f /
        ((h * Real.sqrt (Real.log (1/h)) : ℝ) : ℂ) := by
  have hi := (dilation h hh).inner_map_map (logarithmicIntervalSource 0 h) f
  rw [dilation_intervalSource hh, inner_smul_left, Complex.conj_ofReal] at hi
  have hn : (Real.sqrt h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hh).ne'
  have he : inner ℂ (logarithmicIntervalSource 0 1) (dilation h hh f) =
      inner ℂ (logarithmicIntervalSource 0 h) f / (Real.sqrt h : ℂ) := by
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using hi
  rw [logarithmicCollarRescaling, dif_pos hh, inner_smul_right,
    ← indicatorCutoff_symmetric, unit_intervalSource_cut, he]
  have hs : (Real.sqrt h : ℂ) * (Real.sqrt h : ℂ) = (h : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hh.le
  simp only [Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = inner ℂ (logarithmicIntervalSource 0 h) f *
        ((Real.sqrt h : ℂ) * (Real.sqrt h : ℂ))⁻¹ *
          (Real.sqrt (Real.log (1/h)) : ℂ)⁻¹ := by
            rw [mul_inv_rev]
            ring
    _ = _ := by rw [hs]; ring

private theorem reflection_intervalSource (lo hi : ℝ) :
    l2Reflection (logarithmicIntervalSource lo hi) = logarithmicIntervalSource (-hi) (-lo) := by
  apply Lp.ext
  have hc := (logarithmicIntervalSource_coeFn lo hi).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (logarithmicIntervalSource lo hi), hc,
    logarithmicIntervalSource_coeFn (-hi) (-lo), volume.ae_ne (-lo), volume.ae_ne (-hi)]
      with x hr hc hn hlo hhi
  change logarithmicIntervalSource lo hi (-x) =
    (Ioc lo hi).indicator (fun _ => (1 : ℂ)) (-x) at hc
  rw [hr, hc, hn]
  have he : -x ∈ Ioc lo hi ↔ x ∈ Ioc (-hi) (-lo) := by
    constructor
    · intro hs
      exact ⟨lt_of_le_of_ne (by linarith only [hs.2]) (Ne.symm hhi),
        by linarith only [hs.1]⟩
    · intro hs
      have hx := lt_of_le_of_ne hs.2 hlo
      exact ⟨by linarith only [hx], by linarith only [hs.1]⟩
  simp only [indicator_apply, he]

private theorem intervalSource_positiveExtension (h : ℝ) :
    suzukiPositiveZeroExtension (soninHalfLine (logarithmicIntervalSource 0 h)) =
      logarithmicIntervalSource 0 h := by
  apply suzukiPositiveZeroExtension_soninHalfLine_eq_of_mem_halfLineL2
  rw [mem_halfLineL2_iff]
  filter_upwards [logarithmicIntervalSource_coeFn 0 h] with x hx hn
  rw [hx, indicator_of_notMem (show x ∉ Ioc (0 : ℝ) h from fun hp => (not_lt.mpr hn.le) hp.1)]

private theorem inner_positiveExtension (f g : SuzukiPositiveL2) :
    inner ℂ (suzukiPositiveZeroExtension f) (suzukiPositiveZeroExtension g) = inner ℂ f g := by
  let U : SuzukiPositiveL2 →ₗᵢ[ℂ] SoninL2 :=
    { suzukiPositiveZeroExtensionLinear with norm_map' := norm_suzukiPositiveZeroExtension }
  exact U.inner_map_map f g

namespace WeilHilbertBeforeContact

/-- The actual right residual mean has the exact right endpoint coefficient. -/
theorem evalVectorRightCollarResidual_mean_limit {a c : PrecontactAperture}
    (hac : a.1.1 < c.1.1) (z : ℂ) :
    Tendsto (fun h : ℝ =>
      inner ℂ (logarithmicIntervalSource 0 h)
        (suzukiPositiveZeroExtension (evalVectorRightCollarResidual hac.le z)) /
          ((h*Real.sqrt (Real.log (1/h)) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
        (evalVectorRightEndpointForcing a z : RealLineL2) y)) := by
  have he := (tendsto_const_nhds (x := logarithmicIntervalSource 0 1)).inner
    (evalVectorRightCollarResidual_scaled_limit hac z)
  have hu : inner ℂ (logarithmicIntervalSource 0 1) (logarithmicIntervalSource 0 1) = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
    rw [norm_logarithmicIntervalSource_sq zero_le_one]
    norm_num
  rw [inner_smul_right, hu, mul_one] at he
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact inner_intervalSource_logarithmicCollarRescaling hh _

/-- The reflected left residual mean reads the actual left endpoint coefficient. -/
theorem evalVectorLeftCollarResidual_mean_limit {a c : PrecontactAperture}
    (hac : a.1.1 < c.1.1) (z : ℂ) :
    Tendsto (fun h : ℝ =>
      inner ℂ (logarithmicIntervalSource 0 h)
        (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual hac.le z)) /
          ((h*Real.sqrt (Real.log (1/h)) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
        (evalVectorLeftEndpointForcing a z : RealLineL2) y)) := by
  have he := (tendsto_const_nhds (x := logarithmicIntervalSource 0 1)).inner
    (evalVectorLeftCollarResidual_scaled_limit hac z)
  have hu : inner ℂ (logarithmicIntervalSource 0 1) (logarithmicIntervalSource 0 1) = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
    rw [norm_logarithmicIntervalSource_sq zero_le_one]
    norm_num
  rw [inner_smul_right, hu, mul_one] at he
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact inner_intervalSource_logarithmicCollarRescaling hh _

/-- The right constant collar pairs with the fixed enclosing residual. -/
theorem inner_constantRightCollar_increment {a b c : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1) (z : ℂ) (h : ℝ)
    (r : WeilHilbertBeforeContact b)
    (hr : ccmArchimedeanFormEmbedding b.1 (toForm b r) =
      logarithmicIntervalSource a.1.1 (a.1.1+h)) :
    inner ℂ r (evalVectorIncrement hab z) =
      inner ℂ (logarithmicIntervalSource 0 h)
        (suzukiPositiveZeroExtension (evalVectorRightCollarResidual (hab.trans hbc) z)) := by
  have hp := inner_evalVectorIncrement_rightCollar_in_enclosure hab hbc z r
    (soninHalfLine (logarithmicIntervalSource 0 h)) (by
      rw [intervalSource_positiveExtension, logarithmicIntervalSource_shift]
      exact hr)
  rw [← inner_positiveExtension, intervalSource_positiveExtension] at hp
  exact hp

/-- Reflection gives the same exact pairing for the left constant collar. -/
theorem inner_constantLeftCollar_increment {a b c : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1) (z : ℂ) (h : ℝ)
    (l : WeilHilbertBeforeContact b)
    (hl : ccmArchimedeanFormEmbedding b.1 (toForm b l) =
      logarithmicIntervalSource (-a.1.1-h) (-a.1.1)) :
    inner ℂ l (evalVectorIncrement hab z) =
      inner ℂ (logarithmicIntervalSource 0 h)
        (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual (hab.trans hbc) z)) := by
  have hp := inner_evalVectorIncrement_leftCollar_in_enclosure hab hbc z l
    (soninHalfLine (logarithmicIntervalSource 0 h)) (by
      rw [intervalSource_positiveExtension, logarithmicIntervalSource_shift, reflection_intervalSource]
      simpa only [neg_add, sub_eq_add_neg] using hl)
  rw [← inner_positiveExtension, intervalSource_positiveExtension] at hp
  exact hp

/-- Both literal constant collars are admitted in the enlarged Weil space. -/
theorem exists_constantCollar_pair (b : PrecontactAperture) {a h : ℝ}
    (ha : 0 ≤ a) (hh : 0 < h) (hb : b.1.1 = a+h) :
    ∃ l r : WeilHilbertBeforeContact b,
      ccmArchimedeanFormEmbedding b.1 (toForm b l) =
        logarithmicIntervalSource (-a-h) (-a) ∧
      ccmArchimedeanFormEmbedding b.1 (toForm b r) =
        logarithmicIntervalSource a (a+h) := by
  obtain ⟨l, hl⟩ := exists_ccm_form_of_intervalSource b.1 (-a-h) hh.le (by
    intro x hx
    change -b.1.1 ≤ x ∧ x ≤ b.1.1
    rw [hb]
    constructor <;> linarith only [hx.1, hx.2, ha, hh])
  obtain ⟨r, hr⟩ := exists_ccm_form_of_intervalSource b.1 a hh.le (by
    intro x hx
    change -b.1.1 ≤ x ∧ x ≤ b.1.1
    rw [hb]
    constructor <;> linarith only [hx.1, hx.2, ha, hh])
  refine ⟨fromFormCLM b l, fromFormCLM b r, ?_, ?_⟩
  · simpa only [toForm_fromForm, sub_add_cancel] using hl
  · simpa only [toForm_fromForm] using hr

/-- The two constant collars have the sharp joint leading energy. Their
interaction contributes only a bounded physical-mass correction. -/
theorem constantCollar_pair_energy_upper (c : PrecontactAperture)
    {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (hh1 : h ≤ 1)
    (l r : WeilHilbertBeforeContact c)
    (hl : ccmArchimedeanFormEmbedding c.1 (toForm c l) =
      logarithmicIntervalSource (-a-h) (-a))
    (hr : ccmArchimedeanFormEmbedding c.1 (toForm c r) =
      logarithmicIntervalSource a (a+h)) (α β : ℂ) :
    ‖α • l + β • r‖^2 ≤
      h*(Real.log (1/h)+3+‖weilLogarithmicCorrection c.1‖+weilExteriorCrossingBound c.1)*
        (‖α‖^2+‖β‖^2) := by
  have hl' : ccmArchimedeanFormEmbedding c.1 (toForm c l) =
      logarithmicIntervalSource (-a-h) (-a-h+h) := by
    simpa only [sub_add_cancel] using hl
  have hlE : ‖l‖^2 ≤ h*(Real.log (1/h)+3+‖weilLogarithmicCorrection c.1‖) := by
    rw [norm_sq_eq_weil]
    exact ccmWeilForm_intervalSource_upper c.1 (-a-h) hh hh1 (toForm c l) hl'
  have hrE : ‖r‖^2 ≤ h*(Real.log (1/h)+3+‖weilLogarithmicCorrection c.1‖) := by
    rw [norm_sq_eq_weil]
    exact ccmWeilForm_intervalSource_upper c.1 a hh hh1 (toForm c r) hr
  have hlhalf : ∀ᵐ x ∂volume, 0 < x →
      ccmArchimedeanFormEmbedding c.1 (toForm c l) x = 0 := by
    rw [hl]
    filter_upwards [logarithmicIntervalSource_coeFn (-a-h) (-a)] with x hx hp
    rw [hx, indicator_of_notMem (show x ∉ Ioc (-a-h) (-a) by
      intro hx; linarith only [hx.2, ha, hp])]
  have hrhalf : ∀ᵐ x ∂volume, x < 0 →
      ccmArchimedeanFormEmbedding c.1 (toForm c r) x = 0 := by
    rw [hr]
    filter_upwards [logarithmicIntervalSource_coeFn a (a+h)] with x hx hp
    rw [hx, indicator_of_notMem (show x ∉ Ioc a (a+h) by
      intro hx; linarith only [hx.1, ha, hp])]
  let C := weilExteriorCrossingBound c.1
  have hC : 0 ≤ C := by dsimp only [C, weilExteriorCrossingBound]; positivity
  let X := ‖ccmArchimedeanFormToAperture c.1 (toForm c r)‖
  let Y := ‖ccmArchimedeanFormToAperture c.1 (toForm c l)‖
  have hX : X^2 = h := by
    change ‖ccmArchimedeanFormEmbedding c.1 (toForm c r)‖^2 = h
    rw [hr, norm_logarithmicIntervalSource_sq (by linarith only [hh]), add_sub_cancel_left]
  have hY : Y^2 = h := by
    change ‖ccmArchimedeanFormEmbedding c.1 (toForm c l)‖^2 = h
    rw [hl, norm_logarithmicIntervalSource_sq (by linarith only [hh])]
    ring
  have hXY : X*Y ≤ h := by nlinarith only [hX, hY, sq_nonneg (X-Y)]
  have hcross : ‖inner ℂ l r‖ ≤ C*h := by
    rw [← norm_inner_symm (𝕜 := ℂ) r l, inner_eq_weil]
    have hb := norm_ccmWeilForm_oppositeHalfLines_of_supported c.1
      (toForm c r) (toForm c l) hrhalf hlhalf
    exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hXY hC)
  have hpair : (inner ℂ (α • l) (β • r)).re ≤ ‖α‖*‖β‖*(C*h) := by
    apply (Complex.re_le_norm _).trans
    rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, Complex.norm_conj]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hcross (mul_nonneg (norm_nonneg α) (norm_nonneg β))
  have hα := mul_le_mul_of_nonneg_left hlE (sq_nonneg ‖α‖)
  have hβ := mul_le_mul_of_nonneg_left hrE (sq_nonneg ‖β‖)
  have hCS := mul_nonneg (mul_nonneg hC hh.le) (sq_nonneg (‖α‖-‖β‖))
  rw [norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, mul_pow, mul_pow]
  change _ + 2*(inner ℂ (α • l) (β • r)).re + _ ≤ _
  nlinarith only [hα, hβ, hpair, hCS]

/-- One fixed enclosing aperture bounds every smaller pair of constant collars. -/
theorem constantCollar_pair_energy_upper_in_enclosure {b c : PrecontactAperture}
    (hbc : b.1.1 ≤ c.1.1) {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (hh1 : h ≤ 1)
    (l r : WeilHilbertBeforeContact b)
    (hl : ccmArchimedeanFormEmbedding b.1 (toForm b l) =
      logarithmicIntervalSource (-a-h) (-a))
    (hr : ccmArchimedeanFormEmbedding b.1 (toForm b r) =
      logarithmicIntervalSource a (a+h)) (α β : ℂ) :
    ‖α • l + β • r‖^2 ≤
      h*(Real.log (1/h)+3+‖weilLogarithmicCorrection c.1‖+weilExteriorCrossingBound c.1)*
        (‖α‖^2+‖β‖^2) := by
  have he (u : WeilHilbertBeforeContact b) :
      ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hbc u)) =
        ccmArchimedeanFormEmbedding b.1 (toForm b u) := by
    rw [toForm_inclusion]
    exact ccmArchimedeanFormToAperture_coe_eq_of_val_eq (apertureExt_val hbc (toForm b u))
  have hb := constantCollar_pair_energy_upper c ha hh hh1 (inclusion hbc l) (inclusion hbc r)
    ((he l).trans hl) ((he r).trans hr) α β
  simpa only [← map_smul, ← map_add, (inclusion hbc).norm_map] using hb

/-- Constant collars give a variational lower bound with the same logarithmic
normalization as the exact residual means. -/
theorem constantCollar_trial_lower {a b c : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hb : b.1.1 = a.1.1+h) (z α β : ℂ) :
    2 * (starRingEnd ℂ α *
      (inner ℂ (logarithmicIntervalSource 0 h)
        (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual (hab.trans hbc) z)) /
          ((h*Real.sqrt (Real.log (1/h)) : ℝ) : ℂ)) +
      starRingEnd ℂ β *
      (inner ℂ (logarithmicIntervalSource 0 h)
        (suzukiPositiveZeroExtension (evalVectorRightCollarResidual (hab.trans hbc) z)) /
          ((h*Real.sqrt (Real.log (1/h)) : ℝ) : ℂ))).re -
      (1 + (3+‖weilLogarithmicCorrection c.1‖+weilExteriorCrossingBound c.1) /
        Real.log (1/h)) * (‖α‖^2+‖β‖^2) ≤
      (kernel b z z-kernel a z z).re/h := by
  let L := Real.log (1/h)
  let D := 3+‖weilLogarithmicCorrection c.1‖+weilExteriorCrossingBound c.1
  let S := ‖α‖^2+‖β‖^2
  let mL := inner ℂ (logarithmicIntervalSource 0 h)
    (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual (hab.trans hbc) z)) /
      ((h*Real.sqrt L : ℝ) : ℂ)
  let mR := inner ℂ (logarithmicIntervalSource 0 h)
    (suzukiPositiveZeroExtension (evalVectorRightCollarResidual (hab.trans hbc) z)) /
      ((h*Real.sqrt L : ℝ) : ℂ)
  let P := (starRingEnd ℂ α*mL+starRingEnd ℂ β*mR).re
  change 2*P-(1+D/L)*S ≤ _
  have hL : 0 < L := Real.log_pos ((one_lt_div hh).mpr hh1)
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hsC : (Real.sqrt L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  obtain ⟨l, r, hl, hr⟩ := exists_constantCollar_pair b a.1.2.le hh hb
  let v := α • l+β • r
  let w := (Real.sqrt L : ℂ)⁻¹ • v
  have he := constantCollar_pair_energy_upper_in_enclosure hbc a.1.2 hh hh1.le l r hl hr α β
  have he' : ‖v‖^2 ≤ h*(L+D)*S := by
    convert he using 1 <;> dsimp only [v, L, D, S] <;> ring
  have hw : ‖w‖^2 ≤ h*(1+D/L)*S := by
    have hn : ‖w‖^2 = ‖v‖^2/L := by
      dsimp only [w]
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs, mul_pow, inv_pow, Real.sq_sqrt hL.le]
      ring
    rw [hn]
    calc
      _ ≤ (h*(L+D)*S)/L := div_le_div_of_nonneg_right he' hL.le
      _ = _ := by field_simp; ring
  have hp : (inner ℂ w (evalVectorIncrement hab z)).re = h*P := by
    have hc : inner ℂ w (evalVectorIncrement hab z) =
        (h : ℂ)*(starRingEnd ℂ α*mL+starRingEnd ℂ β*mR) := by
      dsimp only [w, v]
      rw [inner_smul_left, map_inv₀, Complex.conj_ofReal, inner_add_left,
        inner_smul_left, inner_smul_left,
        inner_constantLeftCollar_increment hab hbc z h l hl,
        inner_constantRightCollar_increment hab hbc z h r hr]
      dsimp only [mL, mR]
      push_cast
      field_simp
      <;> ring
    rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hv := sq_nonneg ‖w-evalVectorIncrement hab z‖
  rw [norm_sub_sq (𝕜 := ℂ)] at hv
  change 0 ≤ ‖w‖^2-2*(inner ℂ w (evalVectorIncrement hab z)).re+
    ‖evalVectorIncrement hab z‖^2 at hv
  rw [hp] at hv
  rw [kernel_diagonal_sub_eq_norm_increment_sq hab]
  apply (le_div_iff₀ hh).mpr
  nlinarith only [hv, hw]

#print axioms constantCollar_pair_energy_upper_in_enclosure
#print axioms constantCollar_pair_energy_upper
#print axioms evalVectorRightCollarResidual_mean_limit
#print axioms evalVectorLeftCollarResidual_mean_limit
#print axioms constantCollar_trial_lower
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower

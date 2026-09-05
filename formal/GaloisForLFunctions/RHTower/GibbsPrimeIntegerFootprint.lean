/-
# Full-prime energy versus polynomial-length integer sections

For every fixed `1/2 ≤ sigma < 1`, the full prime-cutoff energy on `[-1,1]`
outgrows every power of the prime aperture. Any bounded-coefficient integer
section of polynomial length is asymptotically energy-negligible relative to
that product: subtracting it leaves an energy ratio tending to one.

This separates two finite approximations. It does not prove a bound for the
literal Möbius integer-prefix Gamma--Hankel energy, and does not prove RH.
-/

import GaloisForLFunctions.RHTower.GibbsFullPrimeGammaEscape
import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall
import GaloisForLFunctions.RHTower.CorrelationBoundsCountNotLocation

open Filter Topology Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

theorem tendsto_fullEulerEscapeExponent_sub_log
    {a : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) (k : ℝ) :
    Tendsto (fun Y => fullEulerEscapeExponent a Y - k * Real.log Y) atTop atTop := by
  have ha1 : a < 1 := by linarith
  have hD := tendsto_eulerLogDeficit ha0 ha2
  have hL2 : Tendsto (fun Y : ℝ => Real.log Y ^ 2) atTop atTop := by
    simpa [pow_two] using Real.tendsto_log_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hDsmall : Tendsto (fun Y : ℝ =>
      eulerLogDeficit a (antiscaleFrequency a Y) Y * Real.log Y / Y ^ a) atTop (nhds 0) := by
    refine (hD.div_atTop hL2).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    have hlog : Real.log Y ≠ 0 := (Real.log_pos hY).ne'
    have hy : Y ^ a ≠ 0 := (Real.rpow_pos_of_pos (by linarith) a).ne'
    field_simp
  have hP := tendsto_primeRpowLogSumLE ha0
  have hsmall := HTGeometry.tendsto_logPow_div_rpow ha0 2
  have hcoefficient : Tendsto (fun Y : ℝ =>
      primeRpowLogSumLE a Y / Y ^ a -
        2 * (eulerLogDeficit a (antiscaleFrequency a Y) Y * Real.log Y / Y ^ a) -
        (k + 2) * (Real.log Y ^ 2 / Y ^ a)) atTop (nhds (1 / a)) := by
    simpa using (hP.sub (hDsmall.const_mul 2)).sub (hsmall.const_mul (k + 2))
  have hscale0 : Tendsto (fun Y : ℝ => Real.log Y / Y ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero
  have hscalePositive : ∀ᶠ Y : ℝ in atTop, Real.log Y / Y ^ a ∈ Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    exact div_pos (Real.log_pos hY) (Real.rpow_pos_of_pos (by linarith) a)
  have hscale : Tendsto (fun Y : ℝ => Y ^ a / Real.log Y) atTop atTop := by
    simpa [Function.comp_def] using tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hscale0, hscalePositive⟩)
  have hmajor := hcoefficient.pos_mul_atTop (one_div_pos.mpr ha0) hscale
  apply tendsto_atTop_mono' _ _ hmajor
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  have hlog : Real.log Y ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hy : Y ^ a ≠ 0 := (Real.rpow_pos_of_pos (by linarith) a).ne'
  have heq :
      (primeRpowLogSumLE a Y / Y ^ a -
        2 * (eulerLogDeficit a (antiscaleFrequency a Y) Y * Real.log Y / Y ^ a) -
        (k + 2) * (Real.log Y ^ 2 / Y ^ a)) * (Y ^ a / Real.log Y) =
      primeRpowLogSumLE a Y / Real.log Y -
        2 * eulerLogDeficit a (antiscaleFrequency a Y) Y - (k + 2) * Real.log Y := by
    field_simp
  rw [heq, fullEulerEscapeExponent]
  linarith [primeRpowLogSumLE_div_log_le_log_positiveEulerSquare ha1 hY]

theorem fullEuler_weighted_energy_div_rpow_tendsto
    (w : ℝ → ℝ) (hw : Continuous w) (hwNonneg : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    {a : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) (k : ℝ) :
    Tendsto (fun Y : ℝ =>
      (∫ t in (-1 : ℝ)..1, w t * eulerMellinNormSq a t Y) / Y ^ k) atTop atTop := by
  have ha1 : a < 1 := by linarith
  obtain ⟨δ, hδ, hfloor⟩ := exists_local_half_floor_of_continuousAt_of_pos hw.continuousAt hw0
  have hsmall : Tendsto (fun Y : ℝ => |antiscaleFrequency a Y| + fullEulerPeakWidth a Y)
      atTop (nhds 0) := by
    simpa using (tendsto_antiscaleFrequency ha0).abs.add (tendsto_fullEulerPeakWidth ha1)
  have hnear : ∀ᶠ Y : ℝ in atTop,
      |antiscaleFrequency a Y| + fullEulerPeakWidth a Y < min δ 1 :=
    hsmall.eventually (gt_mem_nhds (lt_min hδ (by norm_num)))
  have hgrowth : Tendsto (fun Y : ℝ => (w 0 / 8) *
      Real.exp (fullEulerEscapeExponent a Y - k * Real.log Y)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_fullEulerEscapeExponent_sub_log ha0 ha2 k)).const_mul_atTop (by positivity)
  apply tendsto_atTop_mono' _ _ hgrowth
  filter_upwards [hnear, eventually_ge_atTop (2 : ℝ)] with Y hnear hY
  have hd : 0 < fullEulerPeakWidth a Y :=
    div_pos (fullEulerEnvelopeRatio_pos ha1 _ _) (by positivity)
  have hnearδ := hnear.trans_le (min_le_left _ _)
  have hnear1 := hnear.trans_le (min_le_right _ _)
  have hbandAbs : ∀ t ∈ Icc (antiscaleFrequency a Y - fullEulerPeakWidth a Y)
      (antiscaleFrequency a Y + fullEulerPeakWidth a Y), |t| < δ := by
    intro t ht
    have hlo := neg_abs_le (antiscaleFrequency a Y)
    have hhi := le_abs_self (antiscaleFrequency a Y)
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hpeak := fullEulerPeak_weighted_integral_lower w hw ha1 hY
    (show 0 ≤ w 0 / 2 by positivity) (fun t ht => hfloor t (hbandAbs t ht))
  have hcont : Continuous (fun t : ℝ => w t * eulerMellinNormSq a t Y) := by
    unfold eulerMellinNormSq
    fun_prop
  have hnonneg : ∀ t, 0 ≤ w t * eulerMellinNormSq a t Y := by
    intro t
    rw [eulerMellinNormSq_eq_envelope_mul_ratio]
    exact mul_nonneg (hwNonneg t)
      (mul_nonneg (positiveEulerSquare_pos _ _).le (fullEulerEnvelopeRatio_pos ha1 _ _).le)
  have hca : (-1 : ℝ) ≤ antiscaleFrequency a Y - fullEulerPeakWidth a Y := by
    linarith [neg_abs_le (antiscaleFrequency a Y)]
  have hab : antiscaleFrequency a Y - fullEulerPeakWidth a Y ≤
      antiscaleFrequency a Y + fullEulerPeakWidth a Y := by linarith
  have hbd : antiscaleFrequency a Y + fullEulerPeakWidth a Y ≤ 1 := by
    linarith [le_abs_self (antiscaleFrequency a Y)]
  have hmono := intervalIntegral.integral_mono_interval (μ := volume) hca hab hbd
    (Filter.Eventually.of_forall hnonneg) (hcont.intervalIntegrable (-1) 1)
  have hpower : 0 < Y ^ k := Real.rpow_pos_of_pos (by linarith) _
  calc
    _ = ((w 0 / 2) / 4 * Real.exp (fullEulerEscapeExponent a Y)) / Y ^ k := by
      rw [Real.exp_sub, Real.rpow_def_of_pos (by linarith : 0 < Y)]
      rw [mul_comm k (Real.log Y)]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (hpeak.trans hmono) hpower.le

/-- The literal finite prime product on a Mellin line. -/
def fullEulerMellinProduct (a Y t : ℝ) : ℂ :=
  ∏ p ∈ Nat.primesLE ⌊Y⌋₊,
    (1 - (((p : ℝ) ^ (a - 1) : ℝ) : ℂ) *
      Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I))

theorem norm_fullEulerMellinProduct_sq (a Y t : ℝ) :
    ‖fullEulerMellinProduct a Y t‖ ^ 2 = eulerMellinNormSq a t Y := by
  rw [← Complex.normSq_eq_norm_sq, fullEulerMellinProduct, eulerMellinNormSq]
  exact map_prod Complex.normSq _ _

theorem continuous_fullEulerMellinProduct (a Y : ℝ) : Continuous (fullEulerMellinProduct a Y) := by
  unfold fullEulerMellinProduct
  fun_prop

/-- Fixed-window weighted energy, with no normalization of the signal. -/
def mellinWindowEnergy (w : ℝ → ℝ) (F : ℝ → ℂ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, w t * ‖F t‖ ^ 2

theorem mellinWindowEnergy_nonneg (w : ℝ → ℝ) (hw : ∀ t, 0 ≤ w t) (F : ℝ → ℂ) :
    0 ≤ mellinWindowEnergy w F := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg (hw t) (sq_nonneg _)

theorem mellinWindowEnergy_fullEuler_eq (w : ℝ → ℝ) (a Y : ℝ) :
    mellinWindowEnergy w (fullEulerMellinProduct a Y) =
      ∫ t in (-1 : ℝ)..1, w t * eulerMellinNormSq a t Y := by
  simp only [mellinWindowEnergy, norm_fullEulerMellinProduct_sq]

theorem mellinWindowEnergy_perturbation (w : ℝ → ℝ) (hw : Continuous w)
    (hw0 : ∀ t, 0 ≤ w t) (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    {e : ℝ} (he : 0 < e) :
    |mellinWindowEnergy w (F - G) - mellinWindowEnergy w F| ≤
      e * mellinWindowEnergy w F + (1 + 1 / e) * mellinWindowEnergy w G := by
  have hintF : IntervalIntegrable (fun t => w t * ‖F t‖ ^ 2) volume (-1) 1 :=
    (hw.mul (hF.norm.pow 2)).intervalIntegrable _ _
  have hintG : IntervalIntegrable (fun t => w t * ‖G t‖ ^ 2) volume (-1) 1 :=
    (hw.mul (hG.norm.pow 2)).intervalIntegrable _ _
  have hintFG : IntervalIntegrable (fun t => w t * ‖F t - G t‖ ^ 2) volume (-1) 1 :=
    (hw.mul ((hF.sub hG).norm.pow 2)).intervalIntegrable _ _
  have hb (t : ℝ) :
      |w t * ‖F t - G t‖ ^ 2 - w t * ‖F t‖ ^ 2| ≤
        e * (w t * ‖F t‖ ^ 2) + (1 + 1 / e) * (w t * ‖G t‖ ^ 2) := by
    have hpert := sq_norm_perturbation (F t) (-G t)
    simp only [norm_neg, ← sub_eq_add_neg] at hpert
    have hyoung : 2 * ‖F t‖ * ‖G t‖ ≤ e * ‖F t‖ ^ 2 + ‖G t‖ ^ 2 / e := by
      have hs := sq_nonneg (e * ‖F t‖ - ‖G t‖)
      apply (mul_le_mul_iff_left₀ he).mp
      nlinarith [div_mul_cancel₀ (‖G t‖ ^ 2) he.ne']
    simp only [div_eq_mul_inv] at hyoung
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw0 t)]
    have hmul := mul_le_mul_of_nonneg_left (hpert.trans (by
      simp only [div_eq_mul_inv, one_mul]
      nlinarith :
      2 * ‖F t‖ * ‖G t‖ + ‖G t‖ ^ 2 ≤
        e * ‖F t‖ ^ 2 + (1 + 1 / e) * ‖G t‖ ^ 2)) (hw0 t)
    nlinarith
  simp only [mellinWindowEnergy, Pi.sub_apply]
  rw [← intervalIntegral.integral_sub hintFG hintF]
  calc
    _ ≤ ∫ t in (-1 : ℝ)..1,
        |w t * ‖F t - G t‖ ^ 2 - w t * ‖F t‖ ^ 2| := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        intervalIntegral.norm_integral_le_integral_norm (f := fun t =>
          w t * ‖F t - G t‖ ^ 2 - w t * ‖F t‖ ^ 2) (by norm_num : (-1 : ℝ) ≤ 1)
    _ ≤ ∫ t in (-1 : ℝ)..1,
        e * (w t * ‖F t‖ ^ 2) + (1 + 1 / e) * (w t * ‖G t‖ ^ 2) :=
      intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
        ((hintFG.sub hintF).abs) ((hintF.const_mul e).add (hintG.const_mul _))
        (fun t ht => hb t)
    _ = _ := by
      rw [intervalIntegral.integral_add (hintF.const_mul _) (hintG.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- A uniformly bounded signal has the corresponding square bound in every
nonnegative fixed-window weight. -/
theorem mellinWindowEnergy_le_of_norm_le (w : ℝ → ℝ) (hw : Continuous w)
    (hw0 : ∀ t, 0 ≤ w t) (G : ℝ → ℂ) (hG : Continuous G) {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ t ∈ Icc (-1 : ℝ) 1, ‖G t‖ ≤ B) :
    mellinWindowEnergy w G ≤ (∫ t in (-1 : ℝ)..1, w t) * B ^ 2 := by
  calc
    _ ≤ ∫ t in (-1 : ℝ)..1, w t * B ^ 2 := by
      apply intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
        ((hw.mul (hG.norm.pow 2)).intervalIntegrable _ _)
        ((hw.mul_const _).intervalIntegrable _ _)
      intro t ht
      apply mul_le_mul_of_nonneg_left _ (hw0 t)
      change ‖G t‖ ^ 2 ≤ B ^ 2
      nlinarith [hbound t ht, norm_nonneg (G t)]
    _ = _ := intervalIntegral.integral_mul_const _ _

/-- Polynomially bounded signals have vanishing energy relative to the full
prime aperture. This says nothing about boundedness of the signals themselves. -/
theorem fullEuler_polynomial_correction_energy_ratio_zero
    (w : ℝ → ℝ) (hw : Continuous w) (hwNonneg : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    {a : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2)
    (G : ℝ → ℝ → ℂ) (hG : ∀ Y, Continuous (G Y)) (k : ℕ)
    (hbound : ∀ᶠ Y in atTop, ∀ t ∈ Icc (-1 : ℝ) 1, ‖G Y t‖ ≤ Y ^ k) :
    Tendsto (fun Y => mellinWindowEnergy w (G Y) /
      mellinWindowEnergy w (fullEulerMellinProduct a Y)) atTop (nhds 0) := by
  have hgrowth : Tendsto (fun Y =>
      mellinWindowEnergy w (fullEulerMellinProduct a Y) / Y ^ (2 * k)) atTop atTop := by
    simpa only [mellinWindowEnergy_fullEuler_eq, Real.rpow_natCast] using
      fullEuler_weighted_energy_div_rpow_tendsto w hw hwNonneg hw0 ha0 ha2 (2 * k : ℕ)
  have hnum : ∀ᶠ Y in atTop,
      mellinWindowEnergy w (G Y) / Y ^ (2 * k) ≤ ∫ t in (-1 : ℝ)..1, w t := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with Y hY hY0
    apply (div_le_iff₀ (pow_pos hY0 _)).2
    simpa only [pow_mul, mul_comm 2 k] using
      mellinWindowEnergy_le_of_norm_le w hw hwNonneg (G Y) (hG Y)
        (pow_nonneg hY0.le _) hY
  simp only [mul_comm 2 k, pow_mul] at hnum hgrowth
  have hzero := tendsto_bdd_div_atTop_nhds_zero
    (Filter.Eventually.of_forall (fun Y : ℝ =>
      div_nonneg (mellinWindowEnergy_nonneg w hwNonneg (G Y)) (sq_nonneg (Y ^ k))))
    hnum hgrowth
  apply hzero.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  field_simp

/-- Exact positive survivor: a polynomially bounded additive correction leaves
asymptotically all of the full-prime weighted energy. -/
theorem fullEuler_polynomial_correction_residual_ratio_one
    (w : ℝ → ℝ) (hw : Continuous w) (hwNonneg : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    {a : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2)
    (G : ℝ → ℝ → ℂ) (hG : ∀ Y, Continuous (G Y)) (k : ℕ)
    (hbound : ∀ᶠ Y in atTop, ∀ t ∈ Icc (-1 : ℝ) 1, ‖G Y t‖ ≤ Y ^ k) :
    Tendsto (fun Y => mellinWindowEnergy w (fullEulerMellinProduct a Y - G Y) /
      mellinWindowEnergy w (fullEulerMellinProduct a Y)) atTop (nhds 1) := by
  have hzero := fullEuler_polynomial_correction_energy_ratio_zero
    w hw hwNonneg hw0 ha0 ha2 G hG k hbound
  have hinfty : Tendsto (fun Y => mellinWindowEnergy w (fullEulerMellinProduct a Y))
      atTop atTop := by
    simpa only [mellinWindowEnergy_fullEuler_eq] using
      fullEuler_weighted_energy_tendsto w hw hwNonneg hw0 ha0 ha2
  apply Metric.tendsto_nhds.2
  intro d hd
  have he : 0 < d / 2 := by positivity
  have hc : 0 < 1 + 1 / (d / 2) := by positivity
  have hsmall := hzero.eventually (gt_mem_nhds (show 0 < (d / 2) / (1 + 1 / (d / 2)) by positivity))
  filter_upwards [hinfty.eventually_gt_atTop 0, hsmall] with Y hY hsmall
  have hpert := mellinWindowEnergy_perturbation w hw hwNonneg
    (fullEulerMellinProduct a Y) (G Y) (continuous_fullEulerMellinProduct a Y) (hG Y) he
  have hdiv := (div_le_div_of_nonneg_right hpert hY.le)
  have heq :
      ((d / 2) * mellinWindowEnergy w (fullEulerMellinProduct a Y) +
        (1 + 1 / (d / 2)) * mellinWindowEnergy w (G Y)) /
          mellinWindowEnergy w (fullEulerMellinProduct a Y) =
      d / 2 + (1 + 1 / (d / 2)) *
        (mellinWindowEnergy w (G Y) / mellinWindowEnergy w (fullEulerMellinProduct a Y)) := by
    field_simp
  rw [heq] at hdiv
  have hsmall' := (lt_div_iff₀ hc).1 hsmall
  rw [Real.dist_eq]
  calc
    _ = |mellinWindowEnergy w (fullEulerMellinProduct a Y - G Y) -
        mellinWindowEnergy w (fullEulerMellinProduct a Y)| /
          mellinWindowEnergy w (fullEulerMellinProduct a Y) := by
      rw [show mellinWindowEnergy w (fullEulerMellinProduct a Y - G Y) /
          mellinWindowEnergy w (fullEulerMellinProduct a Y) - 1 =
          (mellinWindowEnergy w (fullEulerMellinProduct a Y - G Y) -
          mellinWindowEnergy w (fullEulerMellinProduct a Y)) /
          mellinWindowEnergy w (fullEulerMellinProduct a Y) by field_simp]
      rw [abs_div, abs_of_pos hY]
    _ < d := by linarith

/-- Literal bounded-coefficient integer section; no product closure is taken. -/
def finiteIntegerMellinSection (c : ℕ → ℂ) (sigma : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, c n * ((((n + 1 : ℕ) : ℝ) ^ (-sigma) : ℝ) : ℂ) *
    Complex.exp (((-(t * Real.log (n + 1 : ℕ)) : ℝ) : ℂ) * Complex.I)

theorem continuous_finiteIntegerMellinSection (c : ℕ → ℂ) (sigma : ℝ) (N : ℕ) :
    Continuous (finiteIntegerMellinSection c sigma N) := by
  unfold finiteIntegerMellinSection
  fun_prop

theorem norm_finiteIntegerMellinSection_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (N : ℕ) (t : ℝ) :
    ‖finiteIntegerMellinSection c sigma N t‖ ≤ N := by
  unfold finiteIntegerMellinSection
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖c n * ((((n + 1 : ℕ) : ℝ) ^ (-sigma) : ℝ) : ℂ) *
        Complex.exp (((-(t * Real.log (n + 1 : ℕ)) : ℝ) : ℂ) * Complex.I)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact (mul_le_mul (hc n)
        (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
          (neg_nonpos.mpr hsigma)) (by positivity) (by norm_num)).trans_eq (one_mul _)
    _ = _ := by simp

/-- Every polynomial-length bounded-coefficient integer section is negligible
relative to the full prime product, including at the critical line. -/
theorem fullEuler_integer_section_residual_ratio_one
    (w : ℝ → ℝ) (hw : Continuous w) (hwNonneg : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (k : ℕ)
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma) (hsigma1 : sigma < 1) :
    Tendsto (fun Y => mellinWindowEnergy w
      (fullEulerMellinProduct (1 - sigma) Y - finiteIntegerMellinSection c sigma (⌊Y⌋₊ ^ k)) /
      mellinWindowEnergy w (fullEulerMellinProduct (1 - sigma) Y)) atTop (nhds 1) := by
  apply fullEuler_polynomial_correction_residual_ratio_one w hw hwNonneg hw0
    (by linarith : 0 < 1 - sigma) (by linarith : 1 - sigma ≤ 1 / 2)
    (fun Y => finiteIntegerMellinSection c sigma (⌊Y⌋₊ ^ k))
    (fun Y => continuous_finiteIntegerMellinSection _ _ _) k
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with Y hY
  intro t ht
  calc
    _ ≤ ((⌊Y⌋₊ ^ k : ℕ) : ℝ) := norm_finiteIntegerMellinSection_le c hc (by linarith) _ _
    _ = (⌊Y⌋₊ : ℝ) ^ k := by norm_cast
    _ ≤ Y ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hY) _

/-- The same residual law for the literal archimedean Gamma weight. -/
theorem fullPrimeEulerGamma_integer_section_residual_ratio_one
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (k : ℕ)
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma) (hsigma1 : sigma < 1) :
    Tendsto (fun Y => mellinWindowEnergy
      (fun t => ‖Complex.Gamma ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (fullEulerMellinProduct (1 - sigma) Y - finiteIntegerMellinSection c sigma (⌊Y⌋₊ ^ k)) /
      fullPrimeEulerGammaEnergy sigma Y) atTop (nhds 1) := by
  have hsigma0 : 0 < sigma := by linarith
  have hΓ : Continuous (fun t : ℝ => Complex.Gamma ((sigma : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : ∀ m : ℕ, (sigma : ℂ) + (t : ℂ) * Complex.I ≠ -m := by
      intro m hm
      have h := congrArg Complex.re hm
      simp at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have harg : ContinuousAt (fun u : ℝ => (sigma : ℂ) + (u : ℂ) * Complex.I) t := by
      fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => (sigma : ℂ) + (u : ℂ) * Complex.I)
      (x := t) ((Complex.differentiableAt_Gamma _ hne).continuousAt) harg
  have hw0 : 0 < ‖Complex.Gamma ((sigma : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
    simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.Gamma_ofReal,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact sq_pos_of_pos (Real.Gamma_pos_of_pos hsigma0)
  simpa only [mellinWindowEnergy_fullEuler_eq, fullPrimeEulerGammaEnergy, Pi.pow_apply] using
    fullEuler_integer_section_residual_ratio_one
      (fun t : ℝ => ‖Complex.Gamma ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (hΓ.norm.pow 2) (fun t => sq_nonneg _) hw0
      c hc k hsigma hsigma1

/-- No cancellation assumption: every fixed polynomial-length literal Möbius
section leaves asymptotically all of the full-prime Gamma energy. At `k = 1`
this section is precisely the low-integer part of the squarefree Euler expansion;
for larger `k` it is an additive correction, not the prime-product tail. -/
theorem fullPrimeEulerGamma_mobius_section_residual_ratio_one (k : ℕ)
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma) (hsigma1 : sigma < 1) :
    Tendsto (fun Y => mellinWindowEnergy
      (fun t => ‖Complex.Gamma ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (fullEulerMellinProduct (1 - sigma) Y -
        finiteIntegerMellinSection (fun n => (ArithmeticFunction.moebius (n + 1) : ℂ))
          sigma (⌊Y⌋₊ ^ k)) /
      fullPrimeEulerGammaEnergy sigma Y) atTop (nhds 1) := by
  apply fullPrimeEulerGamma_integer_section_residual_ratio_one _ _ k hsigma hsigma1
  intro n
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)

end RHTower

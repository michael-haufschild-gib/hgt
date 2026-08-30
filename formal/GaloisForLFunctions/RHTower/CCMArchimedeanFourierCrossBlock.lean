import GaloisForLFunctions.RHTower.CCMArchimedeanHankelKernel
import GaloisForLFunctions.RHTower.L2FourierReflection
import GaloisForLFunctions.HTGeometry.SchwartzProduct
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open Complex Filter MeasureTheory Set FourierTransform
open scoped ENNReal InnerProductSpace Real SchwartzMap Topology Convolution FourierTransform

namespace RHTower

local instance cCMArchimedeanFourierCrossBlockLocalInst1 : SFinite ccmPositiveMeasure := by
  unfold ccmPositiveMeasure
  infer_instance

def ccmReflectSchwartz (u : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv) u

@[simp] theorem ccmReflectSchwartz_apply (u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ccmReflectSchwartz u x = u (-x) := rfl

theorem l2Reflection_toLp_ccmReflectSchwartz (u : 𝓢(ℝ, ℂ)) :
    l2Reflection (u.toLp 2 volume) = (ccmReflectSchwartz u).toLp 2 volume := by
  rfl

def ccmNegativeReflectedSchwartz (u : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  (Iio 0).indicator (fun y => u (-y)) x

theorem integrable_ccmNegativeReflectedSchwartz (u : 𝓢(ℝ, ℂ)) :
    Integrable (ccmNegativeReflectedSchwartz u) := by
  have hu : Integrable (fun x : ℝ => u (-x)) := by
    have heq : (fun x : ℝ => u (-x)) = (ccmReflectSchwartz u : ℝ → ℂ) := by
      funext x
      rfl
    rw [heq]
    exact (ccmReflectSchwartz u).integrable
  exact hu.indicator measurableSet_Iio

theorem memLp_ccmNegativeReflectedSchwartz (u : 𝓢(ℝ, ℂ)) :
    MemLp (ccmNegativeReflectedSchwartz u) 2 volume := by
  have hu : MemLp (fun x : ℝ => u (-x)) 2 volume := by
    have heq : (fun x : ℝ => u (-x)) = (ccmReflectSchwartz u : ℝ → ℂ) := by
      funext x
      rfl
    rw [heq]
    exact (ccmReflectSchwartz u).memLp 2 volume
  exact hu.indicator measurableSet_Iio

theorem coe_one_sub_ccmPositiveHalfLineProjection (v : SoninL2) :
    (((1 - ccmPositiveHalfLineProjection) v : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (Iio 0).indicator (fun x => v x) := by
  filter_upwards [Lp.coeFn_sub v (ccmPositiveHalfLineProjection v),
    indicatorCutoff_ae (Ici 0) measurableSet_Ici v] with x hsub hpos
  change ((v - ccmPositiveHalfLineProjection v : SoninL2) : ℝ → ℂ) x = _
  rw [hsub, Pi.sub_apply]
  change (v : ℝ → ℂ) x - (ccmPositiveHalfLineProjection v : ℝ → ℂ) x = _
  change (ccmPositiveHalfLineProjection v : ℝ → ℂ) x = _ at hpos
  rw [hpos]
  by_cases hx : x < 0
  · simp [hx, not_le.mpr hx]
  · simp [hx, le_of_not_gt hx]

theorem ccmNegativeReflectedSchwartz_toLp (u : 𝓢(ℝ, ℂ)) :
    (memLp_ccmNegativeReflectedSchwartz u).toLp (ccmNegativeReflectedSchwartz u) =
      (1 - ccmPositiveHalfLineProjection) (l2Reflection (u.toLp 2 volume)) := by
  apply Lp.ext
  have href := SchwartzMap.coeFn_toLp (ccmReflectSchwartz u) 2 volume
  filter_upwards [MemLp.coeFn_toLp (memLp_ccmNegativeReflectedSchwartz u),
    coe_one_sub_ccmPositiveHalfLineProjection ((ccmReflectSchwartz u).toLp 2 volume),
    href] with x hq hcut hrefx
  rw [hq, l2Reflection_toLp_ccmReflectSchwartz, hcut]
  by_cases hx : x < 0
  · simp [ccmNegativeReflectedSchwartz, hx, hrefx]
  · simp [ccmNegativeReflectedSchwartz, hx]

def ccmHalfLineConvolution (g u : 𝓢(ℝ, ℂ)) : ℝ → ℂ :=
  (g : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ]
    ccmNegativeReflectedSchwartz u

theorem integrable_ccmHalfLineConvolution (g u : 𝓢(ℝ, ℂ)) :
    Integrable (ccmHalfLineConvolution g u) := by
  exact g.integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_ccmNegativeReflectedSchwartz u)

theorem norm_ccmNegativeReflectedSchwartz_le (u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖ccmNegativeReflectedSchwartz u x‖ ≤ SchwartzMap.seminorm ℂ 0 0 u := by
  by_cases hx : x < 0
  · simpa [ccmNegativeReflectedSchwartz, hx] using
      SchwartzMap.norm_le_seminorm ℂ u (-x)
  · simp [ccmNegativeReflectedSchwartz, hx, apply_nonneg]

theorem norm_ccmHalfLineConvolution_le (g u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖ccmHalfLineConvolution g u x‖ ≤
      (∫ y, ‖g y‖) * SchwartzMap.seminorm ℂ 0 0 u := by
  rw [ccmHalfLineConvolution, convolution_def]
  calc
    ‖∫ t, (ContinuousLinearMap.mul ℂ ℂ) (g t)
        (ccmNegativeReflectedSchwartz u (x - t))‖ ≤
        ∫ y, ‖g y‖ * SchwartzMap.seminorm ℂ 0 0 u := by
      apply norm_integral_le_of_norm_le
        (g.integrable.norm.mul_const (SchwartzMap.seminorm ℂ 0 0 u))
      filter_upwards with y
      rw [ContinuousLinearMap.mul_apply', norm_mul]
      gcongr
      exact norm_ccmNegativeReflectedSchwartz_le u (x - y)
    _ = (∫ y, ‖g y‖) * SchwartzMap.seminorm ℂ 0 0 u := by
      rw [integral_mul_const]

theorem memLp_ccmHalfLineConvolution (g u : 𝓢(ℝ, ℂ)) :
    MemLp (ccmHalfLineConvolution g u) 2 volume := by
  let C : ℝ := (∫ y, ‖g y‖) * SchwartzMap.seminorm ℂ 0 0 u
  have hconv := integrable_ccmHalfLineConvolution g u
  rw [memLp_two_iff_integrable_sq_norm hconv.aestronglyMeasurable]
  refine Integrable.mono' (hconv.norm.const_mul C) ?_ ?_
  · exact hconv.aestronglyMeasurable.norm.pow 2
  · filter_upwards with x
    have hx0 : 0 ≤ ‖ccmHalfLineConvolution g u x‖ := norm_nonneg _
    have hxC : ‖ccmHalfLineConvolution g u x‖ ≤ C := by
      simpa [C] using norm_ccmHalfLineConvolution_le g u x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith

/-- Pointwise `L¹` representative of the `L²` Fourier transform for an `L¹ ∩ L²` function. -/
theorem l2_fourier_toLp_coeFn_eq_fourier {a : ℝ → ℂ}
    (ha1 : Integrable a) (ha2 : MemLp a 2 volume) :
    ((fourierUnitary (ha2.toLp a) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => FourierTransform.fourier a ξ := by
  have hcoe := MemLp.coeFn_toLp ha2
  have hcoeInt : Integrable ((ha2.toLp a : SoninL2) : ℝ → ℂ) :=
    ha1.congr hcoe.symm
  have hcoeL1 := MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hcoeInt)
  have hbridge := l2_fourier_coeFn_eq_l1_fourier_of_integrable
    (ha2.toLp a) hcoeInt
  filter_upwards [hbridge] with ξ hξ
  change (((𝓕 (ha2.toLp a)) : SoninL2) : ℝ → ℂ) ξ = _
  rw [hξ, Real.Lp.fourierTransform_apply]
  apply integral_congr_ae
  filter_upwards [hcoeL1, hcoe] with x hxL1 hx
  rw [hxL1, hx]

/-- Time-side convolution operator obtained by conjugating a Schwartz multiplier by Fourier. -/
def ccmTimeFourierMultiplier (f : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
    ccmSchwartzMultiplier f ∘L
      fourierUnitary.toLinearIsometry.toContinuousLinearMap

@[simp] theorem ccmTimeFourierMultiplier_apply (f : 𝓢(ℝ, ℂ)) (v : SoninL2) :
    ccmTimeFourierMultiplier f v =
      fourierUnitary.symm (ccmSchwartzMultiplier f (fourierUnitary v)) := rfl

/-- The literal Fourier multiplier acts on the reflected negative half of a Schwartz vector by the
ordinary convolution with its inverse-transform kernel. -/
theorem ccmTimeFourierMultiplier_negativeReflectedSchwartz
    (g u : 𝓢(ℝ, ℂ)) :
    ccmTimeFourierMultiplier (FourierTransform.fourier g)
        ((memLp_ccmNegativeReflectedSchwartz u).toLp
          (ccmNegativeReflectedSchwartz u)) =
      (memLp_ccmHalfLineConvolution g u).toLp (ccmHalfLineConvolution g u) := by
  apply fourierUnitary.injective
  rw [ccmTimeFourierMultiplier_apply, LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  have hmul := ccmSchwartzMultiplier_coeFn (FourierTransform.fourier g)
    (fourierUnitary ((memLp_ccmNegativeReflectedSchwartz u).toLp
      (ccmNegativeReflectedSchwartz u)))
  have hqFourier := l2_fourier_toLp_coeFn_eq_fourier
    (integrable_ccmNegativeReflectedSchwartz u)
    (memLp_ccmNegativeReflectedSchwartz u)
  have hcFourier := l2_fourier_toLp_coeFn_eq_fourier
    (integrable_ccmHalfLineConvolution g u)
    (memLp_ccmHalfLineConvolution g u)
  filter_upwards [hmul, hqFourier, hcFourier] with ξ hmulξ hqξ hcξ
  rw [hmulξ, hqξ, hcξ, SchwartzMap.fourier_coe]
  exact (Real.fourier_mul_convolution_eq g.integrable
    (integrable_ccmNegativeReflectedSchwartz u) ξ).symm

/-- The convolution with the reflected negative half is exactly the positive Hankel integral. -/
theorem ccmHalfLineConvolution_eq_hankelIntegral (g u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ccmHalfLineConvolution g u x =
      ∫ y, g (x + y) * u y ∂ccmPositiveMeasure := by
  rw [ccmHalfLineConvolution, convolution_mul_swap]
  calc
    (∫ y, g (x - y) * ccmNegativeReflectedSchwartz u y) =
        ∫ y, g (x - (-y)) * ccmNegativeReflectedSchwartz u (-y) :=
      (integral_neg_eq_self
        (fun y => g (x - y) * ccmNegativeReflectedSchwartz u y) volume).symm
    _ = ∫ y in Ioi 0, g (x + y) * u y := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : 0 < y
      · simp [ccmNegativeReflectedSchwartz, hy, neg_lt_zero.mpr hy]
      · have hny : ¬ -y < 0 := by simpa using hy
        simp [ccmNegativeReflectedSchwartz, hy, hny]
    _ = ∫ y in Ici 0, g (x + y) * u y := by
      rw [integral_Ici_eq_integral_Ioi]
    _ = ∫ y, g (x + y) * u y ∂ccmPositiveMeasure := by
      rw [setIntegral_Ici_eq_ccmPositive]

/-- Explicit Schwartz seminorm controlling the value kernel. -/
def ccmValueDecayConstant (g : 𝓢(ℝ, ℂ)) : ℝ :=
  2 ^ 6 * (Finset.Iic (6, 0)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) g

theorem ccmValueDecayConstant_nonneg (g : 𝓢(ℝ, ℂ)) :
    0 ≤ ccmValueDecayConstant g := by
  exact mul_nonneg (by positivity) (apply_nonneg _ _)

theorem ccm_value_decay (g : 𝓢(ℝ, ℂ)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (1 + x + y) ^ 6 * ‖g (x + y)‖ ≤ ccmValueDecayConstant g := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (6, 0)) (k := 6) (n := 0) le_rfl le_rfl g (x + y)
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hx hy)] at h
  rw [norm_iteratedFDeriv_zero] at h
  simpa [ccmValueDecayConstant, add_assoc] using h

theorem ccm_value_l1_majorant (g : 𝓢(ℝ, ℂ)) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖g (x + y)‖ ≤
      ccmValueDecayConstant g * (1 + x ^ 2)⁻¹ * (1 + y ^ 2)⁻¹ := by
  let A : ℝ := 1 + x + y
  let X : ℝ := 1 + x ^ 2
  let Y : ℝ := 1 + y ^ 2
  let d : ℝ := ‖g (x + y)‖
  let C : ℝ := ccmValueDecayConstant g
  have hA : 1 ≤ A := by dsimp [A]; linarith [hx, hy]
  have hX : 0 < X := by dsimp [X]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hxA : X ≤ A ^ 2 := by dsimp [X, A]; nlinarith
  have hyA : Y ≤ A ^ 2 := by dsimp [Y, A]; nlinarith
  have hD : X * Y ≤ A ^ 6 := by
    calc
      X * Y ≤ A ^ 2 * A ^ 2 := by gcongr
      _ = A ^ 4 := by ring
      _ ≤ A ^ 6 := pow_le_pow_right₀ hA (by omega)
  have hdecay : A ^ 6 * d ≤ C := by
    simpa [A, d, C] using ccm_value_decay g hx hy
  change d ≤ C * X⁻¹ * Y⁻¹
  rw [show C * X⁻¹ * Y⁻¹ = C / (X * Y) by field_simp]
  apply (le_div_iff₀ (mul_pos hX hY)).2
  calc
    d * (X * Y) = (X * Y) * d := by ring
    _ ≤ A ^ 6 * d := by gcongr
    _ ≤ C := hdecay

def ccmHankelPairKernel (g u h : 𝓢(ℝ, ℂ)) (x y : ℝ) : ℂ :=
  g (x + y) * u y * starRingEnd ℂ (h x)

theorem integrable_ccmHankelPairKernel (g u h : 𝓢(ℝ, ℂ)) :
    Integrable (Function.uncurry (ccmHankelPairKernel g u h))
      (ccmPositiveMeasure.prod ccmPositiveMeasure) := by
  let C : ℝ := ccmValueDecayConstant g
  let U : ℝ := SchwartzMap.seminorm ℂ 0 0 u
  let H : ℝ := SchwartzMap.seminorm ℂ 0 0 h
  have hC : 0 ≤ C := ccmValueDecayConstant_nonneg g
  have hU : 0 ≤ U := apply_nonneg _ _
  have hH : 0 ≤ H := apply_nonneg _ _
  have hinv : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) ccmPositiveMeasure :=
    integrable_inv_one_add_sq.integrableOn
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      (C * U * H) * (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹)
      (ccmPositiveMeasure.prod ccmPositiveMeasure) := by
    simpa only [mul_assoc] using (hinv.mul_prod hinv).const_mul (C * U * H)
  refine Integrable.mono' hmajor ?_ ?_
  · exact (((g.continuous.comp (continuous_fst.add continuous_snd)).mul
      (u.continuous.comp continuous_snd)).mul
        ((Complex.continuous_conj.comp h.continuous).comp continuous_fst)).aestronglyMeasurable
  · rw [ccmPositiveMeasure, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ici.prod measurableSet_Ici)] with p hp
    have hx : 0 ≤ p.1 := hp.1
    have hy : 0 ≤ p.2 := hp.2
    change ‖ccmHankelPairKernel g u h p.1 p.2‖ ≤
      (C * U * H) * (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹
    rw [ccmHankelPairKernel, norm_mul, norm_mul]
    change ‖g (p.1 + p.2)‖ * ‖u p.2‖ * ‖star (h p.1)‖ ≤ _
    rw [norm_star]
    calc
      ‖g (p.1 + p.2)‖ * ‖u p.2‖ * ‖h p.1‖ ≤
          (C * (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹) * U * H := by
        gcongr
        · simpa [C] using ccm_value_l1_majorant g hx hy
        · exact SchwartzMap.norm_le_seminorm ℂ u p.2
        · exact SchwartzMap.norm_le_seminorm ℂ h p.1
      _ = (C * U * H) * (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹ := by ring

theorem ccm_hankel_pair_fubini (g u h : 𝓢(ℝ, ℂ)) :
    (∫ x, ∫ y, ccmHankelPairKernel g u h x y ∂ccmPositiveMeasure
      ∂ccmPositiveMeasure) =
      ∫ y, ∫ x, ccmHankelPairKernel g u h x y ∂ccmPositiveMeasure
        ∂ccmPositiveMeasure :=
  integral_integral_swap (integrable_ccmHankelPairKernel g u h)

theorem inner_ccmPositiveProjection_halfLineConvolution (g u h : 𝓢(ℝ, ℂ)) :
    inner ℂ (h.toLp 2 volume)
        (ccmPositiveHalfLineProjection
          ((memLp_ccmHalfLineConvolution g u).toLp (ccmHalfLineConvolution g u))) =
      ∫ x, ccmHalfLineConvolution g u x * starRingEnd ℂ (h x)
        ∂ccmPositiveMeasure := by
  have hh := SchwartzMap.coeFn_toLp h 2 volume
  have hc := MemLp.coeFn_toLp (memLp_ccmHalfLineConvolution g u)
  have hcut := indicatorCutoff_ae (Ici 0) measurableSet_Ici
    ((memLp_ccmHalfLineConvolution g u).toLp (ccmHalfLineConvolution g u))
  change ((ccmPositiveHalfLineProjection
      ((memLp_ccmHalfLineConvolution g u).toLp (ccmHalfLineConvolution g u)) :
        SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (Ici 0).indicator (fun x =>
        ((memLp_ccmHalfLineConvolution g u).toLp
          (ccmHalfLineConvolution g u) : SoninL2) x) at hcut
  rw [MeasureTheory.L2.inner_def, ← setIntegral_Ici_eq_ccmPositive,
    ← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [hh, hc, hcut] with x hhx hcx hcutx
  rw [hhx, hcutx]
  by_cases hx : 0 ≤ x
  · have hxmem : x ∈ Ici 0 := hx
    rw [indicator_of_mem hxmem, indicator_of_mem hxmem]
    rw [hcx]
    simp [RCLike.inner_apply]
  · have hx' : x ∉ Ici 0 := hx
    simp [hx']

/-- Matrix coefficient of the cut-off convolution, with both integrations on the positive
half-line, in the same order as the trace-class Hankel operator. -/
theorem inner_ccmPositiveProjection_halfLineConvolution_hankelKernel
    (g u h : 𝓢(ℝ, ℂ)) :
    inner ℂ (h.toLp 2 volume)
        (ccmPositiveHalfLineProjection
          ((memLp_ccmHalfLineConvolution g u).toLp (ccmHalfLineConvolution g u))) =
      ∫ y, u y *
        (∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
  rw [inner_ccmPositiveProjection_halfLineConvolution]
  calc
    (∫ x, ccmHalfLineConvolution g u x * starRingEnd ℂ (h x)
        ∂ccmPositiveMeasure) =
        ∫ x, ∫ y, ccmHankelPairKernel g u h x y ∂ccmPositiveMeasure
          ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ccmHalfLineConvolution_eq_hankelIntegral, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with y
      simp only [ccmHankelPairKernel]
    _ = ∫ y, ∫ x, ccmHankelPairKernel g u h x y ∂ccmPositiveMeasure
          ∂ccmPositiveMeasure := ccm_hankel_pair_fubini g u h
    _ = ∫ y, u y *
        (∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [ccmHankelPairKernel]
      ring

/-- Time-side upper-right block `P (F⁻¹ M_f F) (1-P)`, followed by reflection so both its source
and target use the positive half-line. -/
def ccmPositiveFourierHankelBlock (f : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  ccmPositiveHalfLineProjection ∘L
    ccmTimeFourierMultiplier f ∘L
      (1 - ccmPositiveHalfLineProjection) ∘L l2Reflection

@[simp] theorem ccmPositiveFourierHankelBlock_apply
    (f : 𝓢(ℝ, ℂ)) (v : SoninL2) :
    ccmPositiveFourierHankelBlock f v =
      ccmPositiveHalfLineProjection
        (ccmTimeFourierMultiplier f
          ((1 - ccmPositiveHalfLineProjection) (l2Reflection v))) := rfl

theorem inner_ccmPositiveFourierHankelBlock_fourier
    (g u h : 𝓢(ℝ, ℂ)) :
    inner ℂ (h.toLp 2 volume)
        (ccmPositiveFourierHankelBlock (FourierTransform.fourier g)
          (u.toLp 2 volume)) =
      ∫ y, u y *
        (∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
  rw [ccmPositiveFourierHankelBlock_apply,
    ← ccmNegativeReflectedSchwartz_toLp,
    ccmTimeFourierMultiplier_negativeReflectedSchwartz]
  exact inner_ccmPositiveProjection_halfLineConvolution_hankelKernel g u h

theorem inner_ccmPositiveFourierHankelBlock (f u h : 𝓢(ℝ, ℂ)) :
    inner ℂ (h.toLp 2 volume)
        (ccmPositiveFourierHankelBlock f (u.toLp 2 volume)) =
      ∫ y, u y *
        (∫ x, FourierTransform.fourierInv f (x + y) *
          starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
  have hsource := inner_ccmPositiveFourierHankelBlock_fourier
    (FourierTransform.fourierInv f) u h
  rw [FourierTransform.fourier_fourierInv_eq] at hsource
  exact hsource

/-- Literal Fourier upper-right block, after reflecting its negative source half-line, equals the
trace-class positive Hankel operator constructed from the inverse Fourier transform of the symbol. -/
theorem ccmPositiveFourierHankelBlock_eq_ccmPositiveHankel (f : 𝓢(ℝ, ℂ)) :
    ccmPositiveFourierHankelBlock f =
      ccmPositiveHankel (FourierTransform.fourierInv f) := by
  apply ContinuousLinearMap.ext
  intro v
  let p : SoninL2 → Prop := fun v =>
    ccmPositiveFourierHankelBlock f v =
      ccmPositiveHankel (FourierTransform.fourierInv f) v
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) v
  · exact isClosed_eq (ccmPositiveFourierHankelBlock f).continuous
      (ccmPositiveHankel (FourierTransform.fourierInv f)).continuous
  · intro u
    apply sub_eq_zero.mp
    refine DenseRange.eq_zero_of_inner_right ℂ
      (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) ?_
    intro h
    rw [inner_sub_right]
    change inner ℂ (h.toLp 2 volume)
        (ccmPositiveFourierHankelBlock f (u.toLp 2 volume)) -
      inner ℂ (h.toLp 2 volume)
        (ccmPositiveHankel (FourierTransform.fourierInv f) (u.toLp 2 volume)) = 0
    rw [inner_ccmPositiveFourierHankelBlock,
      inner_ccmPositiveHankel_schwartz, sub_self]

end RHTower

import GaloisForLFunctions.RHTower.CCMArchimedeanHankelTraceClass
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact Hankel kernel of the CCM half-line factorization

This file identifies the trace-class operator constructed in
`CCMArchimedeanHankelTraceClass` with the positive-quadrant Hankel kernel

`(x,y) ↦ g (x+y)`.

The proof is an unconditional Bochner--Fubini argument on Schwartz vectors.  In particular, it
does not assume the boundedness, measurability, integrability, or trace-class property of an
abstract kernel operator: all required estimates are proved from the Schwartz seminorms of `g`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Real SchwartzMap Topology

namespace RHTower

local instance cCMArchimedeanHankelKernelLocalInst1 : SFinite ccmPositiveMeasure := by
  unfold ccmPositiveMeasure
  infer_instance

/-- Region below the diagonal in the positive quadrant, in `(t,y)` order. -/
def ccmVolterraRegion : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}

theorem measurableSet_ccmVolterraRegion : MeasurableSet ccmVolterraRegion := by
  exact measurableSet_le measurable_snd measurable_fst

theorem integrable_ccmVolterra_indicator {F : ℝ → ℝ → ℂ}
    (hF : Integrable (Function.uncurry F) (ccmPositiveMeasure.prod ccmPositiveMeasure)) :
    Integrable (fun p : ℝ × ℝ =>
      ccmVolterraRegion.indicator (Function.uncurry F) p)
      (ccmPositiveMeasure.prod ccmPositiveMeasure) :=
  hF.indicator measurableSet_ccmVolterraRegion

/-- Fubini on the positive Volterra region `0 ≤ y ≤ t`. -/
theorem ccm_positive_volterra_fubini {F : ℝ → ℝ → ℂ}
    (hF : Integrable (Function.uncurry F) (ccmPositiveMeasure.prod ccmPositiveMeasure)) :
    (∫ t, ∫ y, if y ≤ t then F t y else 0 ∂ccmPositiveMeasure
        ∂ccmPositiveMeasure) =
      ∫ y, ∫ t, if y ≤ t then F t y else 0 ∂ccmPositiveMeasure
        ∂ccmPositiveMeasure := by
  let V : ℝ → ℝ → ℂ := fun t y => if y ≤ t then F t y else 0
  have hV : Function.uncurry V =
      ccmVolterraRegion.indicator (Function.uncurry F) := by
    funext p
    by_cases hp : p.2 ≤ p.1
    · have hp' : p ∈ ccmVolterraRegion := hp
      rw [indicator_of_mem hp']
      simp [V, Function.uncurry, hp]
    · have hp' : p ∉ ccmVolterraRegion := hp
      rw [indicator_of_notMem hp']
      simp [V, Function.uncurry, hp]
  have hint : Integrable (Function.uncurry V)
      (ccmPositiveMeasure.prod ccmPositiveMeasure) := by
    rw [hV]
    exact integrable_ccmVolterra_indicator hF
  exact integral_integral_swap hint

theorem setIntegral_Icc_eq_ccmPositive_indicator {F : ℝ → ℂ} {t : ℝ} :
    (∫ y in Icc 0 t, F y) =
      ∫ y, if y ≤ t then F y else 0 ∂ccmPositiveMeasure := by
  rw [ccmPositiveMeasure, ← integral_indicator measurableSet_Icc,
    ← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy0 : 0 ≤ y
  · by_cases hyt : y ≤ t
    · simp [hy0, hyt]
    · simp [hy0, hyt]
  · have hnyt : ¬y ∈ Icc 0 t := fun hy => hy0 hy.1
    simp [hy0, hnyt]

theorem setIntegral_Ici_eq_ccmPositive (F : ℝ → ℂ) :
    (∫ x in Ici 0, F x) = ∫ x, F x ∂ccmPositiveMeasure := by
  rw [ccmPositiveMeasure]

theorem ccmPositive_indicator_eq_setIntegral_Ici {F : ℝ → ℂ} {y : ℝ} (hy : 0 ≤ y) :
    (∫ t, if y ≤ t then F t else 0 ∂ccmPositiveMeasure) =
      ∫ t in Ici y, F t := by
  rw [ccmPositiveMeasure, ← integral_indicator measurableSet_Ici,
    ← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards with t
  by_cases hyt : y ≤ t
  · have ht0 : 0 ≤ t := hy.trans hyt
    simp [hyt, ht0]
  · have hnt : t ∉ Ici y := hyt
    simp [hyt, hnt]

/-- Separable inverse-quadratic majorant for the translated derivative of a Schwartz function. -/
theorem ccm_deriv_l1_majorant (g : 𝓢(ℝ, ℂ)) {x t : ℝ}
    (hx : 0 ≤ x) (ht : 0 ≤ t) :
    ‖deriv g (x + t)‖ ≤
      ccmDerivativeDecayConstant g * (1 + x ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by
  let A : ℝ := 1 + x + t
  let X : ℝ := 1 + x ^ 2
  let T : ℝ := 1 + t ^ 2
  let d : ℝ := ‖deriv g (x + t)‖
  let C : ℝ := ccmDerivativeDecayConstant g
  have hA : 1 ≤ A := by dsimp [A]; linarith [hx, ht]
  have hX : 0 < X := by dsimp [X]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hxA : X ≤ A ^ 2 := by dsimp [X, A]; nlinarith
  have htA : T ≤ A ^ 2 := by dsimp [T, A]; nlinarith
  have hD : X * T ≤ A ^ 6 := by
    calc
      X * T ≤ A ^ 2 * A ^ 2 := by gcongr
      _ = A ^ 4 := by ring
      _ ≤ A ^ 6 := pow_le_pow_right₀ hA (by omega)
  have hdecay : A ^ 6 * d ≤ C := by
    simpa [A, d, C] using ccm_deriv_decay g hx ht
  change d ≤ C * X⁻¹ * T⁻¹
  rw [show C * X⁻¹ * T⁻¹ = C / (X * T) by field_simp]
  apply (le_div_iff₀ (mul_pos hX hT)).2
  calc
    d * (X * T) = (X * T) * d := by ring
    _ ≤ A ^ 6 * d := by gcongr
    _ ≤ C := hdecay

/-- Scalar integrand obtained by pairing the derivative synthesis slice with `h`. -/
def ccmDerivativePairKernel (g h : 𝓢(ℝ, ℂ)) (t x : ℝ) : ℂ :=
  -(deriv g (x + t)) * starRingEnd ℂ (h x)

theorem integrable_ccmDerivativePairKernel (g h : 𝓢(ℝ, ℂ)) :
    Integrable (Function.uncurry (ccmDerivativePairKernel g h))
      (ccmPositiveMeasure.prod ccmPositiveMeasure) := by
  let C : ℝ := ccmDerivativeDecayConstant g
  let H : ℝ := SchwartzMap.seminorm ℂ 0 0 h
  have hC : 0 ≤ C := ccmDerivativeDecayConstant_nonneg g
  have hH : 0 ≤ H := apply_nonneg _ _
  have hinv : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) ccmPositiveMeasure := by
    exact integrable_inv_one_add_sq.integrableOn
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      (C * H) * (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹)
      (ccmPositiveMeasure.prod ccmPositiveMeasure) := by
    simpa only [mul_assoc] using (hinv.mul_prod hinv).const_mul (C * H)
  refine Integrable.mono' hmajor ?_ ?_
  · have hd : Continuous (fun p : ℝ × ℝ => deriv g (p.2 + p.1)) := by
      have hd' := (SchwartzMap.derivCLM ℂ ℂ g).continuous.comp
        (continuous_snd.add continuous_fst)
      convert hd' using 1
      funext p
      rw [Function.comp_apply, SchwartzMap.derivCLM_apply]
      simp only [Pi.add_apply]
    have hh : Continuous (fun p : ℝ × ℝ => starRingEnd ℂ (h p.2)) := by
      fun_prop
    exact (hd.neg.mul hh).aestronglyMeasurable
  · rw [ccmPositiveMeasure, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ici.prod measurableSet_Ici)] with p hp
    have htp : 0 ≤ p.1 := hp.1
    have hxp : 0 ≤ p.2 := hp.2
    change ‖ccmDerivativePairKernel g h p.1 p.2‖ ≤
      (C * H) * (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹
    rw [ccmDerivativePairKernel, norm_mul, norm_neg]
    change ‖deriv g (p.2 + p.1)‖ * ‖star (h p.2)‖ ≤ _
    rw [norm_star]
    calc
      ‖deriv g (p.2 + p.1)‖ * ‖h p.2‖ ≤
          (C * (1 + p.2 ^ 2)⁻¹ * (1 + p.1 ^ 2)⁻¹) * H := by
        gcongr
        · simpa [C] using ccm_deriv_l1_majorant g hxp htp
        · exact SchwartzMap.norm_le_seminorm ℂ h p.2
      _ = (C * H) * (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹ := by ring

def ccmDerivativePairTail (g h : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  ∫ x, ccmDerivativePairKernel g h t x ∂ccmPositiveMeasure

theorem integrable_ccmDerivativePairTail (g h : 𝓢(ℝ, ℂ)) :
    Integrable (ccmDerivativePairTail g h) ccmPositiveMeasure := by
  exact (integrable_ccmDerivativePairKernel g h).integral_prod_left

def ccmVolterraPairKernel (f g h : 𝓢(ℝ, ℂ)) (t y : ℝ) : ℂ :=
  f y * ccmDerivativePairTail g h t

theorem integrable_ccmVolterraPairKernel (f g h : 𝓢(ℝ, ℂ)) :
    Integrable (Function.uncurry (ccmVolterraPairKernel f g h))
      (ccmPositiveMeasure.prod ccmPositiveMeasure) := by
  have hf : Integrable (f : ℝ → ℂ) ccmPositiveMeasure := f.integrable.integrableOn
  have hJ := integrable_ccmDerivativePairTail g h
  refine (hJ.mul_prod hf).congr (ae_of_all _ fun p => ?_)
  simp [ccmVolterraPairKernel, Function.uncurry, mul_comm]

/-- The derivative tail created by the Volterra factor is the translated Hankel kernel. -/
theorem integral_indicator_ccmDerivativePairTail (g h : 𝓢(ℝ, ℂ))
    {y : ℝ} (hy : 0 ≤ y) :
    (∫ t, if y ≤ t then ccmDerivativePairTail g h t else 0 ∂ccmPositiveMeasure) =
      ∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure := by
  let Gy : ℝ → ℝ → ℂ := fun t x =>
    if y ≤ t then ccmDerivativePairKernel g h t x else 0
  have hGy : Integrable (Function.uncurry Gy)
      (ccmPositiveMeasure.prod ccmPositiveMeasure) := by
    have hbase := integrable_ccmDerivativePairKernel g h
    have hind := hbase.indicator
      ((measurableSet_Ici : MeasurableSet (Ici y)).prod MeasurableSet.univ)
    refine hind.congr (ae_of_all _ fun p => ?_)
    by_cases hyt : y ≤ p.1
    · simp [Gy, Function.uncurry, ccmDerivativePairKernel, hyt]
    · simp [Gy, Function.uncurry, ccmDerivativePairKernel, hyt]
  have hswap := integral_integral_swap hGy
  have hleft : (∫ t, ∫ x, Gy t x ∂ccmPositiveMeasure ∂ccmPositiveMeasure) =
      ∫ t, if y ≤ t then ccmDerivativePairTail g h t else 0
        ∂ccmPositiveMeasure := by
    apply integral_congr_ae
    filter_upwards with t
    by_cases hyt : y ≤ t
    · simp [Gy, ccmDerivativePairTail, hyt]
    · simp [Gy, hyt]
  have hright : (∫ x, ∫ t, Gy t x ∂ccmPositiveMeasure ∂ccmPositiveMeasure) =
      ∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure := by
    apply integral_congr_ae
    filter_upwards with x
    calc
      (∫ t, Gy t x ∂ccmPositiveMeasure) =
          (∫ t, if y ≤ t then -(deriv g (x + t)) else 0
            ∂ccmPositiveMeasure) * starRingEnd ℂ (h x) := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with t
        by_cases hyt : y ≤ t
        · simp [Gy, ccmDerivativePairKernel, hyt]
        · simp [Gy, ccmDerivativePairKernel, hyt]
      _ = (∫ t in Ici y, -(deriv g (x + t))) * starRingEnd ℂ (h x) := by
        rw [ccmPositive_indicator_eq_setIntegral_Ici hy]
      _ = g (x + y) * starRingEnd ℂ (h x) := by
        rw [integral_Ici_eq_integral_Ioi, integral_neg_deriv_schwartz_tail]
  rw [← hleft, hswap, hright]

theorem ccm_factorized_integrand_eq (g h : 𝓢(ℝ, ℂ)) (F : ℂ) (t : ℝ) :
    (((1 + t ^ 2)⁻¹ : ℂ) * F) *
        (∫ x in Ici 0,
          (-(1 + t ^ 2) * deriv g (x + t)) * starRingEnd ℂ (h x)) =
      F * ccmDerivativePairTail g h t := by
  have hinner :
      (∫ x in Ici 0,
        (-(1 + t ^ 2) * deriv g (x + t)) * starRingEnd ℂ (h x)) =
        (1 + t ^ 2 : ℂ) * ccmDerivativePairTail g h t := by
    rw [setIntegral_Ici_eq_ccmPositive, ccmDerivativePairTail,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [ccmDerivativePairKernel]
    ring
  rw [hinner]
  have hw : (1 + t ^ 2 : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + t ^ 2 : ℝ) ≠ 0)
  field_simp

/-- Exact positive-quadrant Hankel kernel formula for the trace-class factorization.

This is an equality of matrix coefficients of the actual bounded operator on the dense family of
Schwartz vectors; neither side is introduced as an assumed kernel operator.
-/
theorem inner_ccmPositiveHankel_schwartz (f g h : 𝓢(ℝ, ℂ)) :
    inner ℂ (h.toLp 2 volume) (ccmPositiveHankel g (f.toLp 2 volume)) =
      ∫ y, f y *
        (∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
  have hfrep := SchwartzMap.coeFn_toLp f 2 volume
  have hhrep := SchwartzMap.coeFn_toLp h 2 volume
  have hfIcc (t : ℝ) :
      (∫ y in Icc 0 t, (f.toLp 2 volume) y) = ∫ y in Icc 0 t, f y := by
    apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [hfrep] with y hy
    intro _
    exact hy
  have hhIci (t : ℝ) :
      (∫ x in Ici 0,
        (-(1 + t ^ 2) * deriv g (x + t)) *
          starRingEnd ℂ ((h.toLp 2 volume) x)) =
        ∫ x in Ici 0,
          (-(1 + t ^ 2) * deriv g (x + t)) * starRingEnd ℂ (h x) := by
    apply setIntegral_congr_ae measurableSet_Ici
    filter_upwards [hhrep] with x hx
    intro _
    rw [hx]
  calc
    inner ℂ (h.toLp 2 volume) (ccmPositiveHankel g (f.toLp 2 volume)) =
        ∫ t,
          (((1 + t ^ 2)⁻¹ : ℂ) * ∫ y in Icc 0 t, f y) *
            (∫ x in Ici 0,
              (-(1 + t ^ 2) * deriv g (x + t)) * starRingEnd ℂ (h x))
          ∂ccmPositiveMeasure := by
      rw [inner_ccmPositiveHankel_integral]
      apply integral_congr_ae
      filter_upwards with t
      rw [hfIcc t, hhIci t]
    _ = ∫ t, (∫ y in Icc 0 t, f y) * ccmDerivativePairTail g h t
          ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      exact ccm_factorized_integrand_eq g h _ t
    _ = ∫ t, ∫ y, if y ≤ t then ccmVolterraPairKernel f g h t y else 0
          ∂ccmPositiveMeasure ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      rw [setIntegral_Icc_eq_ccmPositive_indicator, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hyt : y ≤ t
      · simp [ccmVolterraPairKernel, hyt]
      · simp [hyt]
    _ = ∫ y, ∫ t, if y ≤ t then ccmVolterraPairKernel f g h t y else 0
          ∂ccmPositiveMeasure ∂ccmPositiveMeasure :=
      ccm_positive_volterra_fubini (integrable_ccmVolterraPairKernel f g h)
    _ = ∫ y, f y *
          (∫ t, if y ≤ t then ccmDerivativePairTail g h t else 0
            ∂ccmPositiveMeasure) ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      by_cases hyt : y ≤ t
      · simp [ccmVolterraPairKernel, hyt]
      · simp [hyt]
    _ = ∫ y, f y *
        (∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
      rw [integral_indicator_ccmDerivativePairTail g h hy]

end RHTower

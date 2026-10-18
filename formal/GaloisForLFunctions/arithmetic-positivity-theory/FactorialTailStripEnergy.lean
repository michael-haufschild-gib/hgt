import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailVerticalEnergy
import GaloisForLFunctions.«arithmetic-positivity-theory».ZeroDiskOverlap
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Finite logarithmic area energy on the enlarged Mellin strip. Integrability
is proved by Fubini before the strip integral is used in zero sampling. -/

open MeasureTheory Set
namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

/-- The literal readout energy, extended by zero outside the enlarged sampling strip. -/
def factorialTailStripDensity (n : ℕ) (s : ℂ) : ℝ :=
  zeroSamplingStrip.indicator
    (fun z : ℂ => (1+Real.log (2+|z.im|))*‖factorialTailReadout n z‖^2) s

private def stripProductDensity (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  (Icc (-1/4 : ℝ) (5/4)).indicator
    (fun σ => factorialTailVerticalDensity n σ p.2) p.1

private theorem vertical_nonneg (n : ℕ) (σ t : ℝ) :
    0 ≤ factorialTailVerticalDensity n σ t := by
  unfold factorialTailVerticalDensity
  have hl : 0 ≤ Real.log (2+|t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  positivity

private theorem stripProductDensity_nonneg (n : ℕ) (p : ℝ × ℝ) :
    0 ≤ stripProductDensity n p := by
  classical
  by_cases hp : p.1 ∈ Icc (-1/4 : ℝ) (5/4)
  · simpa only [stripProductDensity,indicator_of_mem hp] using vertical_nonneg n p.1 p.2
  · simp only [stripProductDensity,indicator_of_notMem hp,le_refl]

private theorem stripProductDensity_measurable (n : ℕ) :
    Measurable (stripProductDensity n) := by
  classical
  let S : Set (ℝ × ℝ) := Icc (-1/4 : ℝ) (5/4) ×ˢ univ
  have hS : MeasurableSet S := measurableSet_Icc.prod MeasurableSet.univ
  have hc : ContinuousOn (fun p : ℝ × ℝ =>
      factorialTailReadout n ((p.1 : ℂ)+(p.2 : ℂ)*Complex.I)) S := by
    apply (factorialTailReadout_analyticOnNhd n).continuousOn.comp
      (show Continuous (fun p : ℝ × ℝ => (p.1 : ℂ)+(p.2 : ℂ)*Complex.I) by fun_prop).continuousOn
    intro p hp
    change -1 < ((p.1 : ℂ)+(p.2 : ℂ)*Complex.I).re
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    have := hp.1.1
    linarith
  have hl : Continuous (fun p : ℝ × ℝ => Real.log (2+|p.2|)) := by
    apply Continuous.log (by fun_prop)
    intro p
    positivity
  have hd : ContinuousOn (fun p : ℝ × ℝ => factorialTailVerticalDensity n p.1 p.2) S :=
    ((continuous_const.add hl).continuousOn).mul (hc.norm.pow 2)
  have hm := hd.measurable_piecewise
    (show ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Sᶜ from continuous_const.continuousOn) hS
  convert hm using 1
  funext p
  by_cases hp : p.1 ∈ Icc (-1/4 : ℝ) (5/4)
  · simp [stripProductDensity,S,hp]
  · simp [stripProductDensity,S,hp]

private theorem stripProductDensity_line (n : ℕ) (σ : ℝ) :
    Integrable (fun t : ℝ => stripProductDensity n (σ,t)) := by
  classical
  by_cases hσ : σ ∈ Icc (-1/4 : ℝ) (5/4)
  · simpa only [stripProductDensity,indicator_of_mem hσ] using
      factorialTailVertical_integrable n ⟨σ,hσ⟩
  · simp only [stripProductDensity,indicator_of_notMem hσ]
    exact integrable_zero _ _ _

private theorem stripProductDensity_line_le (n : ℕ) (σ : ℝ) :
    (∫ t : ℝ, stripProductDensity n (σ,t)) ≤
      (Icc (-1/4 : ℝ) (5/4)).indicator
        (fun _ => factorialTailVerticalConstant*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ)) σ := by
  classical
  by_cases hσ : σ ∈ Icc (-1/4 : ℝ) (5/4)
  · simpa only [stripProductDensity,indicator_of_mem hσ] using
      factorialTailVertical_integral_le n ⟨σ,hσ⟩
  · simp only [stripProductDensity,indicator_of_notMem hσ,integral_zero,le_refl]

private theorem stripProductDensity_integrable_and_le (n : ℕ) :
    Integrable (stripProductDensity n) ∧
      (∫ p : ℝ × ℝ, stripProductDensity n p) ≤
        (3/2)*factorialTailVerticalConstant*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ) := by
  let B := factorialTailVerticalConstant*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ)
  let b : ℝ → ℝ := (Icc (-1/4 : ℝ) (5/4)).indicator (fun _ => B)
  have hb : Integrable b := (integrable_indicator_iff measurableSet_Icc).mpr
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc)
  have hm : AEStronglyMeasurable (stripProductDensity n)
      ((volume : Measure ℝ).prod volume) := (stripProductDensity_measurable n).aestronglyMeasurable
  have hnorm : (fun σ : ℝ => ∫ t : ℝ, ‖stripProductDensity n (σ,t)‖) =
      (fun σ : ℝ => ∫ t : ℝ, stripProductDensity n (σ,t)) := by
    funext σ
    apply integral_congr_ae
    filter_upwards [] with t
    exact Real.norm_of_nonneg (stripProductDensity_nonneg n (σ,t))
  have hout : Integrable (fun σ : ℝ => ∫ t : ℝ, ‖stripProductDensity n (σ,t)‖) := by
    apply hb.mono' hm.norm.integral_prod_right'
    filter_upwards [] with σ
    rw [congrFun hnorm σ,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun t => stripProductDensity_nonneg n (σ,t)))]
    exact stripProductDensity_line_le n σ
  have hi : Integrable (stripProductDensity n) :=
    (integrable_prod_iff hm).mpr ⟨Filter.Eventually.of_forall (stripProductDensity_line n),hout⟩
  refine ⟨hi,?_⟩
  have hi' : Integrable (stripProductDensity n) ((volume : Measure ℝ).prod volume) := hi
  have hprod : (∫ p : ℝ × ℝ,stripProductDensity n p) =
      ∫ σ : ℝ,∫ t : ℝ,stripProductDensity n (σ,t) := integral_prod _ hi'
  rw [hprod]
  have hbound := integral_mono hi'.integral_prod_left hb (stripProductDensity_line_le n)
  have he : (∫ σ : ℝ,b σ) = (3/2)*B := by
    dsimp [b]
    rw [integral_indicator_const _ measurableSet_Icc]
    norm_num [Measure.real,Real.volume_Icc]
  rw [he] at hbound
  exact hbound.trans_eq (by dsimp [B]; ring)

private theorem stripProductDensity_coordinates (n : ℕ) (s : ℂ) :
    stripProductDensity n (s.re,s.im) = factorialTailStripDensity n s := by
  classical
  by_cases hs : s ∈ zeroSamplingStrip
  · have hr : s.re ∈ Icc (-1/4 : ℝ) (5/4) := hs
    simp only [stripProductDensity,indicator_of_mem hr,factorialTailStripDensity,
      indicator_of_mem hs,factorialTailVerticalDensity,Complex.re_add_im]
  · have hr : s.re ∉ Icc (-1/4 : ℝ) (5/4) := hs
    simp only [stripProductDensity,indicator_of_notMem hr,factorialTailStripDensity,
      indicator_of_notMem hs]

/-- The full logarithmically weighted area density is integrable on the actual strip. -/
theorem factorialTailStrip_integrable (n : ℕ) : Integrable (factorialTailStripDensity n) := by
  have h := Complex.volume_preserving_equiv_real_prod.integrable_comp_of_integrable
    (stripProductDensity_integrable_and_le n).1
  simpa only [Function.comp_def,Complex.measurableEquivRealProd_apply,
    stripProductDensity_coordinates] using h

/-- The finite strip width preserves the logarithmic source scale. -/
theorem factorialTailStrip_integral_le (n : ℕ) :
    (∫ s : ℂ, factorialTailStripDensity n s) ≤
      (3/2)*factorialTailVerticalConstant*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ) := by
  have he := Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding (stripProductDensity n)
  simp only [Complex.measurableEquivRealProd_apply,stripProductDensity_coordinates] at he
  rw [he]
  exact (stripProductDensity_integrable_and_le n).2

end
end GaloisForLFunctions.ArithmeticPositivityTheory

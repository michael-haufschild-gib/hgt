import GaloisForLFunctions.RHTower.PaperThetaCutPrimitive
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.HTGeometry.EntireDividedDifferenceContour
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Exact transform of the charged, two-ended theta kernel

Integration by parts retains the cut jump. Thus the transform identity is
valid at every pair of complex parameters, without a zero or domain premise.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile HTGeometry GaloisForLFunctions.HTGeometry

def cutThetaTransform (z w : ℂ) : ℂ :=
  ∫ x, flatCharDensity w x*cutQuotient z 0 x

def cutPrimitiveTransform (z w : ℂ) : ℂ :=
  ∫ x, sourceChar w x*cutPrimitive z x

private theorem sourceChar_hasDerivAt (w : ℂ) (x : ℝ) :
    HasDerivAt (sourceChar w) (I*w*sourceChar w x) x := by
  change HasDerivAt (fun y : ℝ => exp (I*w*(y : ℂ))) (I*w*exp (I*w*(x : ℂ))) x
  have h := (((hasDerivAt_id (x : ℂ)).const_mul (I*w)).cexp).comp_ofReal
  simpa [mul_comm] using h

theorem cutThetaTransform_primitive (z w : ℂ) :
    cutThetaTransform z w = -(I*z)*cutPrimitiveTransform z w-flatConnection w := by
  have he : (fun x => flatCharDensity w x*cutQuotient z 0 x) =
      fun x => -(I*z)*(sourceChar w x*cutPrimitive z x)-flatCharDensity w x := by
    funext x
    have h := cutPrimitive_source_formula z x
    dsimp [flatCharDensity]
    linear_combination sourceChar w x*h
  rw [cutThetaTransform, he,
    integral_sub ((integrable_sourceChar_cutPrimitive z w).const_mul _)
      (integrable_flatCharDensity_all w), integral_const_mul]
  rfl

theorem cutPrimitiveTransform_current (z w : ℂ) :
    I*w*cutPrimitiveTransform z w+cutThetaTransform z w = -flatConnection z := by
  let D : ℝ → ℂ := fun x =>
    (I*w*sourceChar w x)*cutPrimitive z x+
      sourceChar w x*((thetaSource.normalized x : ℂ)*cutQuotient z 0 x)
  have he : D = fun x => I*w*(sourceChar w x*cutPrimitive z x)+
      flatCharDensity w x*cutQuotient z 0 x := by
    funext x
    dsimp [D, flatCharDensity]
    ring
  have hi : Integrable D := by
    rw [he]
    exact ((integrable_sourceChar_cutPrimitive z w).const_mul _).add
      (integrable_flatCharDensity_cutQuotient z w)
  have hright : Tendsto (fun x => sourceChar w x*cutPrimitive z x)
      (𝓝[>] (0 : ℝ)) (𝓝 (flatPrimitiveMode z 0)) := by
    have h := ((continuous_sourceChar w).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).mul (tendsto_cutPrimitive_right z)
    simpa [sourceChar] using h
  have hleft : Tendsto (fun x => sourceChar w x*cutPrimitive z x)
      (𝓝[<] (0 : ℝ)) (𝓝 (-flatPrimitiveMode (-z) 0)) := by
    have h := ((continuous_sourceChar w).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (0 : ℝ) ≤ 𝓝 0)).mul (tendsto_cutPrimitive_left z)
    simpa [sourceChar] using h
  have hri : (∫ x in Ioi (0 : ℝ), D x) = -flatPrimitiveMode z 0 := by
    simpa only [zero_sub] using integral_Ioi_deriv_mul_eq_sub
      (fun x _ => sourceChar_hasDerivAt w x)
      (fun x hx => hasDerivAt_cutPrimitive (z := z) (ne_of_gt hx)) hi.integrableOn
      hright (tendsto_sourceChar_cutPrimitive_atTop z w)
  have hli : (∫ x in Iic (0 : ℝ), D x) = -flatPrimitiveMode (-z) 0 := by
    simpa only [sub_zero] using integral_Iic_deriv_mul_eq_sub
      (fun x _ => sourceChar_hasDerivAt w x)
      (fun x hx => hasDerivAt_cutPrimitive (z := z) (ne_of_lt hx)) hi.integrableOn
      hleft (tendsto_sourceChar_cutPrimitive_atBot z w)
  have hs := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (b := (0 : ℝ))
    hi.integrableOn hi.integrableOn
  rw [hli, hri] at hs
  have hd : (∫ x, D x) = -flatConnection z := by
    rw [← hs, ← cutPrimitive_jump]
    ring
  rw [he, integral_add ((integrable_sourceChar_cutPrimitive z w).const_mul _)
    (integrable_flatCharDensity_cutQuotient z w), integral_const_mul] at hd
  exact hd

/-- The full Xi divided-difference law, including coincident parameters. -/
theorem cutThetaTransform_equation (z w : ℂ) :
    (w-z)*cutThetaTransform z w =
      (z*XiC z-w*XiC w)/(thetaSource.mass : ℂ) := by
  have h₁ := cutPrimitiveTransform_current z w
  have h₂ := cutThetaTransform_primitive z w
  have h : (w-z)*cutThetaTransform z w = z*flatConnection z-w*flatConnection w := by
    linear_combination -z*h₁+w*h₂
  rw [h, flatConnection_eq_all, flatConnection_eq_all]
  ring

private theorem norm_flatCharDensity_le_pair {w : ℂ} {B : ℝ}
    (hw : |w.im| ≤ B) (x : ℝ) :
    ‖flatCharDensity w x‖ ≤
      ‖flatCharDensity (-(B : ℂ)*I) x‖+‖flatCharDensity ((B : ℂ)*I) x‖ := by
  have hp : -w.im ≤ B := (neg_le_abs w.im).trans hw
  have hn : w.im ≤ B := (le_abs_self w.im).trans hw
  simp only [norm_flatCharDensity, mul_im, neg_im, ofReal_im, ofReal_re,
    I_re, I_im, mul_zero, mul_one, add_zero, neg_zero, neg_re, neg_neg]
  have he : Real.exp (-w.im*x) ≤ Real.exp (B*x)+Real.exp (-B*x) := by
    rcases le_total 0 x with hx | hx
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hp hx)).trans
        (le_add_of_nonneg_right (Real.exp_nonneg _))
    · have hm : -w.im*x ≤ -B*x := by nlinarith
      exact (Real.exp_le_exp.mpr hm).trans
        (le_add_of_nonneg_left (Real.exp_nonneg _))
  simpa only [mul_add] using mul_le_mul_of_nonneg_left he (thetaSource.normalized_pos x).le

private theorem differentiable_bounded_thetaTransform {f : ℝ → ℂ} {C : ℝ}
    (hf : AEStronglyMeasurable f) (hC : ∀ x, ‖f x‖ ≤ C) :
    Differentiable ℂ (fun w => ∫ x, flatCharDensity w x*f x) := by
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  intro w₀
  let B := ‖w₀‖+1
  let majorant : ℝ → ℝ := fun x => C*
    (‖flatCharDensity (-(B : ℂ)*I) x‖+‖flatCharDensity ((B : ℂ)*I) x‖)
  apply differentiableAt_integral_of_cauchy_dominated (R := 1) (bound := majorant) one_pos
  · intro w _
    exact (continuous_flatCharDensity w).aestronglyMeasurable.mul hf
  · intro x
    dsimp [flatCharDensity, sourceChar]
    fun_prop
  · intro x w hw
    have hd : ‖w-w₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hn : ‖w‖ ≤ B := by
      have h := norm_add_le (w-w₀) w₀
      rw [sub_add_cancel] at h
      dsimp [B]
      linarith
    have hi := (Complex.abs_im_le_norm w).trans hn
    calc
      ‖flatCharDensity w x*f x‖ = ‖flatCharDensity w x‖*‖f x‖ := norm_mul _ _
      _ ≤ ‖flatCharDensity w x‖*C := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
      _ ≤ (‖flatCharDensity (-(B : ℂ)*I) x‖+
          ‖flatCharDensity ((B : ℂ)*I) x‖)*C :=
        mul_le_mul_of_nonneg_right (norm_flatCharDensity_le_pair hi x) hC0
      _ = majorant x := mul_comm _ _
  · exact ((integrable_flatCharDensity_all (-(B : ℂ)*I)).norm.add
      (integrable_flatCharDensity_all ((B : ℂ)*I)).norm).const_mul C

theorem differentiable_cutThetaTransform (z : ℂ) : Differentiable ℂ (cutThetaTransform z) := by
  apply differentiable_bounded_thetaTransform (C := ‖z‖*stripTailControl |z.im| 0+1)
    (measurable_cutQuotient z 0).aestronglyMeasurable
  intro x
  have h := cutQuotient_add_one_strip (z := z) le_rfl x
  have ht := norm_sub_le (cutQuotient z 0 x+1) (1 : ℂ)
  rw [add_sub_cancel_right, norm_one] at ht
  linarith

/-- The actual, everywhere-defined theta transform is a removable divided difference. -/
theorem cutThetaTransform_eq_dslope (z w : ℂ) :
    cutThetaTransform z w =
      -dslope (fun v => v*XiC v) z w/(thetaSource.mass : ℂ) := by
  have hc : Continuous (fun w => -dslope (fun v => v*XiC v) z w/(thetaSource.mass : ℂ)) :=
    ((differentiable_entire_dslope (differentiable_id.mul XiC_differentiable) z).continuous.neg).div_const _
  have he : cutThetaTransform z = fun w =>
      -dslope (fun v => v*XiC v) z w/(thetaSource.mass : ℂ) := by
    apply Continuous.ext_on (dense_compl_singleton z) (differentiable_cutThetaTransform z).continuous hc
    intro v hv
    have hvz : v ≠ z := hv
    apply mul_left_cancel₀ (sub_ne_zero.mpr hvz)
    change (v-z)*cutThetaTransform z v =
      (v-z)*(-dslope (fun u => u*XiC u) z v/(thetaSource.mass : ℂ))
    rw [cutThetaTransform_equation, dslope_of_ne _ hvz, slope_def_field]
    have hm : (thetaSource.mass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero
    field_simp [sub_ne_zero.mpr hvz]
    ring
  exact congrFun he w

end RHTower.PaperThetaEndpoint

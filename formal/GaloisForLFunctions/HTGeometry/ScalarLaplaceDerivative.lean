import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Laplace integration by parts with both original endpoint terms retained. -/
open MeasureTheory Set Filter
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

def scalarLaplaceDamp (w : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-w*(t:ℂ))*f t

/-- Linear polynomial growth with an exponential weight gives the full strict Laplace chamber. -/
theorem scalarLaplaceDamp_integrable_of_linear_growth (f : ℝ → ℂ) (hf : Continuous f)
    (C D r : ℝ) (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ (C+D*t)*Real.exp (r*t))
    (w : ℂ) (hw : r < w.re) :
    IntegrableOn (scalarLaplaceDamp w f) (Ioi 0) := by
  have h₀ := integrableOn_exp_mul_Ioi (show r-w.re < 0 by linarith) 0
  have h₁ : IntegrableOn (fun t : ℝ => t*Real.exp ((r-w.re)*t)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 1) (p := 1) (b := w.re-r) (by norm_num) le_rfl (by linarith)
    simpa only [Real.rpow_one,neg_sub] using h
  have hm : IntegrableOn (fun t : ℝ => (C+D*t)*Real.exp ((r-w.re)*t)) (Ioi 0) := by
    simpa only [IntegrableOn,add_mul,mul_assoc,Pi.add_def] using (h₀.const_mul C).add (h₁.const_mul D)
  apply hm.mono' ((by unfold scalarLaplaceDamp; fun_prop : Continuous (scalarLaplaceDamp w f)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  dsimp only [scalarLaplaceDamp]
  rw [norm_mul,Complex.norm_exp]
  have hr : (-w*(t:ℂ)).re = -w.re*t := by simp
  rw [hr]
  calc
    _ ≤ Real.exp (-w.re*t)*((C+D*t)*Real.exp (r*t)) :=
      mul_le_mul_of_nonneg_left (hb t ht.le) (Real.exp_pos _).le
    _ = (C+D*t)*Real.exp ((r-w.re)*t) := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring

/-- Integrability of the weighted function and derivative derives the boundary limit at infinity. -/
theorem scalarLaplace_derivative (f f' : ℝ → ℂ) (w : ℂ)
    (hd : ∀ t, HasDerivAt f (f' t) t)
    (hf : IntegrableOn (scalarLaplaceDamp w f) (Ioi 0))
    (hf' : IntegrableOn (scalarLaplaceDamp w f') (Ioi 0)) :
    (∫ t in Ioi (0:ℝ), scalarLaplaceDamp w f' t) =
      w*(∫ t in Ioi (0:ℝ), scalarLaplaceDamp w f t)-f 0 := by
  have he (t : ℝ) : HasDerivAt (scalarLaplaceDamp w f)
      (scalarLaplaceDamp w f' t-w*scalarLaplaceDamp w f t) t := by
    have h := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-w)).cexp).mul (hd t)
    convert h using 1 <;> first | rfl | (dsimp [scalarLaplaceDamp]; ring)
  have hi := hf'.sub (hf.const_mul w)
  have hl := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun t _ => he t) hi hf
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => he t) hi hl
  rw [integral_sub hf' (hf.const_mul w),integral_const_mul] at h
  simp only [scalarLaplaceDamp,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,zero_sub] at h
  dsimp only [scalarLaplaceDamp]
  linear_combination h

/-- The second derivative transform retains both physical initial data. -/
theorem scalarLaplace_second_derivative (f v g : ℝ → ℂ) (w : ℂ)
    (hf : ∀ t, HasDerivAt f (v t) t) (hv : ∀ t, HasDerivAt v (g t) t)
    (hfi : IntegrableOn (scalarLaplaceDamp w f) (Ioi 0))
    (hvi : IntegrableOn (scalarLaplaceDamp w v) (Ioi 0))
    (hgi : IntegrableOn (scalarLaplaceDamp w g) (Ioi 0)) :
    (∫ t in Ioi (0:ℝ), scalarLaplaceDamp w g t) =
      w^2*(∫ t in Ioi (0:ℝ), scalarLaplaceDamp w f t)-w*f 0-v 0 := by
  rw [scalarLaplace_derivative v g w hv hvi hgi,
    scalarLaplace_derivative f v w hf hfi hvi]
  ring

end
end GaloisForLFunctions.HTGeometry

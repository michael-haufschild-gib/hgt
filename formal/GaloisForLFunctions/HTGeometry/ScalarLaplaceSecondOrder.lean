import GaloisForLFunctions.HTGeometry.ScalarLaplaceDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-! Scalar second-order Laplace equations derived from function and acceleration growth. -/
open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Acceleration growth controls velocity without an assumed asymptotic boundary value. -/
theorem velocity_bound_of_acceleration (v g : ℝ → ℂ) (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hd : ∀ t, HasDerivAt v (g t) t)
    (hb : ∀ t : ℝ, 0 ≤ t → ‖g t‖ ≤ C*Real.exp (r*t))
    (t : ℝ) (ht : 0 ≤ t) :
    ‖v t‖ ≤ (‖v 0‖+C*t)*Real.exp (r*t) := by
  have hm : ‖v t-v 0‖ ≤ C*Real.exp (r*t)*t := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := 0) (b := t) (f := v) (f' := g) (C := C*Real.exp (r*t))
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => (hb x hx.1).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2.le hr)) hC))
      t ⟨ht,le_rfl⟩
    simpa only [sub_zero] using h
  have he := Real.one_le_exp (mul_nonneg hr ht)
  calc
    ‖v t‖ ≤ ‖v t-v 0‖+‖v 0‖ := by simpa only [add_comm] using norm_le_insert' (v t) (v 0)
    _ ≤ C*Real.exp (r*t)*t+‖v 0‖ := add_le_add hm le_rfl
    _ ≤ C*Real.exp (r*t)*t+‖v 0‖*Real.exp (r*t) := by
      gcongr
      exact le_mul_of_one_le_right (norm_nonneg _) he
    _ = (‖v 0‖+C*t)*Real.exp (r*t) := by ring

/-- Function and acceleration growth suffice for the exact second-order Laplace law. -/
theorem scalarLaplace_second_of_growth (f v g : ℝ → ℂ) (r A C : ℝ)
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hf : ∀ t, HasDerivAt f (v t) t) (hv : ∀ t, HasDerivAt v (g t) t)
    (hg : Continuous g)
    (hfb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ A*Real.exp (r*t))
    (hgb : ∀ t : ℝ, 0 ≤ t → ‖g t‖ ≤ C*Real.exp (r*t))
    (w : ℂ) (hw : r < w.re) :
    (∫ t in Ioi (0:ℝ), scalarLaplaceDamp w g t) =
      w^2*(∫ t in Ioi (0:ℝ), scalarLaplaceDamp w f t)-w*f 0-v 0 := by
  apply scalarLaplace_second_derivative f v g w hf hv
  · exact scalarLaplaceDamp_integrable_of_linear_growth f (continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)) A 0 r
      (by simpa using hfb) w hw
  · exact scalarLaplaceDamp_integrable_of_linear_growth v (continuous_iff_continuousAt.mpr (fun t => (hv t).continuousAt)) ‖v 0‖ C r
      (velocity_bound_of_acceleration v g r C hr hC hv hgb) w hw
  · exact scalarLaplaceDamp_integrable_of_linear_growth g hg C 0 r (by simpa using hgb) w hw

end
end GaloisForLFunctions.HTGeometry

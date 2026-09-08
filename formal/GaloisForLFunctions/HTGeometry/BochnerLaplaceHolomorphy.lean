import GaloisForLFunctions.HTGeometry.ExpRayL2
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Absolute Bochner Laplace convergence gives bounds and interior holomorphy. -/
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def bochnerLaplaceRay (S : ℝ → H) (w : ℂ) : H :=
  ∫ t in Ioi (0 : ℝ), expRay w t • S t

theorem expRay_smul_norm_le (S : ℝ → H) (c : ℝ) (w : ℂ) (hw : c ≤ w.re)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖expRay w t • S t‖ ≤ ‖expRay (c : ℂ) t • S t‖ := by
  simp only [norm_smul,norm_expRay,Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (norm_nonneg _)

theorem bochnerLaplaceRay_integrable {S : ℝ → H} (hS : AEStronglyMeasurable S volume)
    {c : ℝ} (hc : IntegrableOn (fun t => expRay (c : ℂ) t • S t) (Ioi 0))
    (w : ℂ) (hw : c ≤ w.re) :
    IntegrableOn (fun t => expRay w t • S t) (Ioi 0) := by
  apply Integrable.mono hc
  · exact ((show Continuous (expRay w) by unfold expRay; fun_prop).aestronglyMeasurable.smul hS).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact expRay_smul_norm_le S c w hw t ht.le

theorem bochnerLaplaceRay_norm_le {S : ℝ → H} {c : ℝ}
    (hc : IntegrableOn (fun t => expRay (c : ℂ) t • S t) (Ioi 0))
    (w : ℂ) (hw : c ≤ w.re) :
    ‖bochnerLaplaceRay S w‖ ≤ ∫ t in Ioi (0 : ℝ), ‖expRay (c : ℂ) t • S t‖ := by
  apply norm_integral_le_of_norm_le hc.norm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact expRay_smul_norm_le S c w hw t ht.le

private theorem derivative_bound (S : ℝ → H) (c ε : ℝ) (hε : 0 < ε)
    (w : ℂ) (hw : c+ε ≤ w.re) (t : ℝ) (ht : 0 ≤ t) :
    ‖(-(t : ℂ)*expRay w t) • S t‖ ≤ ε⁻¹ * ‖expRay (c : ℂ) t • S t‖ := by
  have he : (ε*t)*Real.exp (-(ε*t)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans (Real.exp_le_one_iff.mpr (by norm_num))
  have he' : t*Real.exp (-(ε*t)) ≤ ε⁻¹ := by
    have hi : ε*ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
    nlinarith
  have hsplit : Real.exp (-((c+ε)*t)) = Real.exp (-(ε*t))*Real.exp (-(c*t)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [norm_smul,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht,norm_expRay,Complex.ofReal_re]
  calc
    t*Real.exp (-(w.re*t))*‖S t‖ ≤ t*Real.exp (-((c+ε)*t))*‖S t‖ := by gcongr
    _ ≤ ε⁻¹*(Real.exp (-(c*t))*‖S t‖) := by
      rw [hsplit]
      nlinarith [mul_le_mul_of_nonneg_right he'
        (mul_nonneg (Real.exp_pos (-(c*t))).le (norm_nonneg (S t)))]

/-- Holomorphy follows from absolute convergence at one strictly smaller real frequency. -/
theorem bochnerLaplaceRay_differentiableAt {S : ℝ → H}
    (hS : AEStronglyMeasurable S volume) {c : ℝ}
    (hc : IntegrableOn (fun t => expRay (c : ℂ) t • S t) (Ioi 0))
    (w : ℂ) (hw : c < w.re) : DifferentiableAt ℂ (bochnerLaplaceRay S) w := by
  let ε : ℝ := (w.re-c)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hm (z : ℂ) : AEStronglyMeasurable (fun t => expRay z t • S t)
      (volume.restrict (Ioi 0)) :=
    ((show Continuous (expRay z) by unfold expRay; fun_prop).aestronglyMeasurable.smul hS).restrict
  have hm' : AEStronglyMeasurable (fun t : ℝ => (-(t : ℂ)*expRay w t) • S t)
      (volume.restrict (Ioi 0)) :=
    ((show Continuous (fun t : ℝ => -(t : ℂ)*expRay w t) by unfold expRay; fun_prop).aestronglyMeasurable.smul hS).restrict
  have hb : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ z ∈ Metric.ball w ε,
      ‖(-(t : ℂ)*expRay z t) • S t‖ ≤ ε⁻¹*‖expRay (c : ℂ) t • S t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    apply derivative_bound S c ε hε z _ t ht.le
    have hr := Complex.abs_re_le_norm (z-w)
    have hd : ‖z-w‖ < ε := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
    simp only [Complex.sub_re] at hr
    have := (abs_lt.mp (hr.trans_lt hd)).1
    dsimp [ε] at this ⊢
    linarith
  have hd : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ z ∈ Metric.ball w ε,
      HasDerivAt (fun y => expRay y t • S t) ((-(t : ℂ)*expRay z t) • S t) z := by
    filter_upwards [] with t z _
    have he := (((hasDerivAt_id z).mul_const (t : ℂ)).neg.cexp).smul_const (S t)
    convert he using 1 <;> simp [expRay,mul_comm]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds w hε) (Eventually.of_forall hm)
    (bochnerLaplaceRay_integrable hS hc w hw.le) hm' hb
    (hc.norm.const_mul ε⁻¹) hd).2.differentiableAt

end
end GaloisForLFunctions.HTGeometry

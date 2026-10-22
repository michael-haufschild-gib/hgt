import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspPositiveMean
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral

/-! Absolute strip admission from the actual horizontal norm mean in the original hyperbolic measure. -/
open Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
noncomputable section

/-- The actual upper-half-plane chart, including its fixed outside value, is measurable. -/
theorem cuspOfComplex_measurable : Measurable (ofComplex : ℂ → UpperHalfPlane) := by
  apply measurableEmbedding_coe.measurable_comp_iff.mp
  change Measurable (fun w : ℂ => (ofComplex w : ℂ))
  have he : (fun w : ℂ => (ofComplex w : ℂ)) =
      fun w : ℂ => if 0 < w.im then w else (ofComplex 0 : ℂ) := by
    funext w
    by_cases hw : 0 < w.im
    · rw [if_pos hw,ofComplex_apply_of_im_pos hw]
    · rw [if_neg hw,ofComplex_apply_eq_of_im_nonpos (le_of_not_gt hw) (by simp : (0:ℂ).im ≤ 0)]
  rw [he]
  exact Measurable.ite (measurableSet_Ioi.preimage Complex.continuous_im.measurable)
    measurable_id measurable_const

theorem cuspStripPoint_measurable : Measurable (fun p : ℝ × ℝ => ofComplex (⟨p.2,p.1⟩:ℂ)) := by
  apply cuspOfComplex_measurable.comp
  have he : (fun p : ℝ × ℝ => (⟨p.2,p.1⟩:ℂ)) =
      fun p : ℝ × ℝ => (p.2:ℂ)+(p.1:ℂ)*Complex.I := by
    funext p
    exact Complex.ext (by simp) (by simp)
  rw [he]
  fun_prop

theorem cuspStripChartIntegrand_measurable (F : UpperHalfPlane → ℂ) (hf : Measurable F) :
    Measurable (stripChartIntegrand F) :=
  ((measurable_fst.pow_const 2).inv).smul (hf.comp cuspStripPoint_measurable)

/-- The actual horizontal norm mean is measurable before any integrability is assumed. -/
theorem cuspHorizontalNormMean_measurable (F : UpperHalfPlane → ℂ) (hf : Measurable F) :
    Measurable (fun y : ℝ => ∫ x in Ico (0:ℝ) 1, ‖F (ofComplex (⟨x,y⟩:ℂ))‖) :=
  ((hf.comp cuspStripPoint_measurable).norm.stronglyMeasurable.integral_prod_right).measurable

/-- Fubini admits the original strip once its actual horizontal norm density is integrable. -/
theorem modularStrip_integrable_of_norm_mean (F : UpperHalfPlane → ℂ) (hf : Measurable F)
    (hline : ∀ y : ℝ, 0 < y →
      IntegrableOn (fun x : ℝ => F (ofComplex (⟨x,y⟩:ℂ))) (Ico (0:ℝ) 1))
    (hmean : IntegrableOn (fun y : ℝ => (y^(2 : ℕ))⁻¹*
      ∫ x in Ico (0:ℝ) 1, ‖F (ofComplex (⟨x,y⟩:ℂ))‖) (Ioi (0:ℝ))) :
    IntegrableOn F modularStrip volume := by
  rw [integrableOn_modularStrip_iff,Measure.volume_eq_prod,IntegrableOn,← Measure.prod_restrict]
  apply (integrable_prod_iff (cuspStripChartIntegrand_measurable F hf).aestronglyMeasurable).mpr
  constructor
  · apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro y hy
    exact (hline y hy).smul ((y^(2 : ℕ))⁻¹)
  · apply hmean.congr_fun _ measurableSet_Ioi
    intro y _
    simp only [stripChartIntegrand,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (y^(2 : ℕ))⁻¹),integral_const_mul]

end
end RHTower.D4BMModularCore

import GaloisForLFunctions.HTGeometry.PoincareSeriesPeterssonIntegrand
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Absolute hyperbolic strip admission from the actual lower and upper height bounds. -/
open Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
noncomputable section

/-- A bounded upper tail and a strictly integrable lower power admit the full strip density. -/
theorem modularStrip_integrable_of_two_bounds (F : UpperHalfPlane → ℂ) (hf : Continuous F)
    (r C D : ℝ) (hr : 1 < r)
    (hlo : ∀ z : UpperHalfPlane, z ∈ modularStrip → z.im ≤ 4 → ‖F z‖ ≤ C*z.im^r)
    (hhi : ∀ z : UpperHalfPlane, z ∈ modularStrip → 4 < z.im → ‖F z‖ ≤ D) :
    IntegrableOn F modularStrip volume := by
  rw [integrableOn_modularStrip_iff,Measure.volume_eq_prod]
  let Q := stripChartIntegrand F
  have hc := continuousOn_stripChartIntegrand hf
  have h1 : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ico (0:ℝ) 1)) :=
    integrableOn_const (by simp)
  have hsmall : IntegrableOn Q (Ioc (0:ℝ) 4 ×ˢ Ico (0:ℝ) 1) (volume.prod volume) := by
    have hg : Integrable (fun y : ℝ => C*y^(r-2)) (volume.restrict (Ioc (0:ℝ) 4)) :=
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r-2)
        (a := (0:ℝ)) (b := 4)).1).const_mul C
    have hG := hg.mul_prod h1
    rw [Measure.prod_restrict] at hG
    apply hG.mono
      ((hc.mono (fun p hp => ⟨hp.1.1,hp.2⟩)).aestronglyMeasurable
        (measurableSet_Ioc.prod measurableSet_Ico))
    apply ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ico)
    intro p hp
    have hy : 0 < p.1 := hp.1.1
    let z := ofComplex (⟨p.2,p.1⟩ : ℂ)
    have him : z.im = p.1 := by rw [show z = ofComplex (⟨p.2,p.1⟩:ℂ) from rfl,
      ofComplex_apply_of_im_pos (by simpa using hy)]; rfl
    have hmem : z ∈ modularStrip := by
      dsimp [z]
      rw [ofComplex_apply_of_im_pos (by simpa using hy)]
      exact hp.2
    have hb := hlo z hmem (by rw [him]; exact hp.1.2)
    rw [him] at hb
    change ‖(p.1^2)⁻¹ • F z‖ ≤ ‖C*p.1^(r-2)*1‖
    simp only [norm_smul,Real.norm_eq_abs,mul_one]
    rw [abs_of_pos (inv_pos.mpr (sq_pos_of_pos hy))]
    calc
      (p.1^2)⁻¹*‖F z‖ ≤ (p.1^2)⁻¹*(C*p.1^r) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C*p.1^(r-2) := by rw [Real.rpow_sub hy,Real.rpow_two]; ring
      _ ≤ |C*p.1^(r-2)| := le_abs_self _
  have hlarge : IntegrableOn Q (Ioi (4:ℝ) ×ˢ Ico (0:ℝ) 1) (volume.prod volume) := by
    have hg : Integrable (fun y : ℝ => D*y^(-2:ℝ)) (volume.restrict (Ioi (4:ℝ))) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) (by norm_num : (0:ℝ)<4)).const_mul D
    have hG := hg.mul_prod h1
    rw [Measure.prod_restrict] at hG
    apply hG.mono
      ((hc.mono (fun p hp => ⟨lt_trans (by norm_num : (0:ℝ)<4) hp.1,hp.2⟩)).aestronglyMeasurable
        (measurableSet_Ioi.prod measurableSet_Ico))
    apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ico)
    intro p hp
    have hy : 0 < p.1 := lt_trans (by norm_num : (0:ℝ)<4) hp.1
    let z := ofComplex (⟨p.2,p.1⟩ : ℂ)
    have him : z.im = p.1 := by rw [show z = ofComplex (⟨p.2,p.1⟩:ℂ) from rfl,
      ofComplex_apply_of_im_pos (by simpa using hy)]; rfl
    have hmem : z ∈ modularStrip := by
      dsimp [z]
      rw [ofComplex_apply_of_im_pos (by simpa using hy)]
      exact hp.2
    have hb := hhi z hmem (by rw [him]; exact hp.1)
    change ‖(p.1^2)⁻¹ • F z‖ ≤ ‖D*p.1^(-2:ℝ)*1‖
    simp only [norm_smul,Real.norm_eq_abs,mul_one]
    rw [abs_of_pos (inv_pos.mpr (sq_pos_of_pos hy))]
    calc
      (p.1^2)⁻¹*‖F z‖ ≤ (p.1^2)⁻¹*D := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = D*p.1^(-2:ℝ) := by rw [Real.rpow_neg hy.le,Real.rpow_two]; ring
      _ ≤ |D*p.1^(-2:ℝ)| := le_abs_self _
  apply (hsmall.union hlarge).mono_set
  intro p hp
  by_cases hy : p.1 ≤ 4
  · exact Or.inl ⟨⟨hp.1,hy⟩,hp.2⟩
  · exact Or.inr ⟨lt_of_not_ge hy,hp.2⟩

end
end RHTower.D4BMModularCore

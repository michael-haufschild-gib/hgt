import GaloisForLFunctions.RHTower.SelbergEisensteinBounds
import GaloisForLFunctions.RHTower.SelbergEisensteinBoundary
import GaloisForLFunctions.RHTower.SelbergModularHyperbolicArea
import GaloisForLFunctions.RHTower.SelbergMaassCellCurvature

/-!
# Exact finite mass budget of the actual positive Eisenstein power family

The proved amplitude bound and literal finite hyperbolic area give integrable
positive mass. Original derivative bounds give integrable positive curvature
and decay of the actual top current. Modular Stokes and full-domain exhaustion
then give integral(q)=lambda*integral(a) for every positive lambda. All densities
come from the original smooth Eisenstein function and its actual derivatives.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ENNReal
namespace GaloisForLFunctions.RHTower.SelbergEisensteinMass
open _root_.RHTower SelbergMaassMean SelbergMaassTraceEnergy SelbergPowerCurvature
  SelbergEisensteinBounds SelbergEisensteinBoundary SelbergModularPotentialGreen
  SelbergModularDomainSlices SelbergMaassFullCurvatureBudget SelbergModularHyperbolicArea
  SelbergMaassCellCurvature
noncomputable section

private theorem point_im (x y : ℝ) : (point x y).im = y := by simp [point]
private theorem chart_continuous : Continuous (fun p : ℝ × ℝ => point p.1 p.2) := by
  unfold point
  fun_prop

/-- The literal hyperbolic model mass in real modular coordinates. -/
def massDensity (lam : Ioi (0 : ℝ)) (p : ℝ × ℝ) : ℝ := model lam (point p.1 p.2) / p.2 ^ 2

/-- The literal hyperbolic model curvature density in real modular coordinates. -/
def curveDensity (lam : Ioi (0 : ℝ)) (p : ℝ × ℝ) : ℝ := curvature lam (point p.1 p.2) / p.2 ^ 2

/-- Every model has a finite explicit amplitude bound on the full closed modular domain. -/
theorem model_bound (lam : Ioi (0 : ℝ)) {p : ℝ × ℝ} (hp : p ∈ fullDomain) :
    model lam (point p.1 p.2) ≤ (1 / 2 : ℝ) ^ (-(lam : ℝ) / 2) := by
  have hl : (0 : ℝ) < (lam : ℝ) := lam.2
  have hy := fullDomain_height_pos hp
  have hb : (1 / 2 : ℝ) ≤ p.2 := (arcHeight_half_le hp.1).trans hp.2
  exact (model_le_height lam ⟨p.1, p.2, hy⟩).trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hb (by linarith))

/-- The actual model mass density is strictly positive throughout the full domain. -/
theorem mass_pos (lam : Ioi (0 : ℝ)) {p : ℝ × ℝ} (hp : p ∈ fullDomain) : 0 < massDensity lam p :=
  div_pos (model_pos lam (by simpa only [point_im] using fullDomain_height_pos hp))
    (sq_pos_of_pos (fullDomain_height_pos hp))

/-- Actual model mass is continuous at every point of the full modular domain. -/
theorem mass_continuousOn (lam : Ioi (0 : ℝ)) : ContinuousOn (massDensity lam) fullDomain := by
  intro p hp
  have hy := fullDomain_height_pos hp
  have hz : 0 < (point p.1 p.2).im := by simpa only [point_im] using hy
  have hc := (((model_c2 lam).continuousOn).continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).comp (f := fun q : ℝ × ℝ => point q.1 q.2) chart_continuous.continuousAt
  exact (hc.div ((continuous_snd.pow 2).continuousAt) (pow_ne_zero 2 hy.ne')).continuousWithinAt

/-- Finite hyperbolic area and the proved value bound discharge full original-model integrability. -/
theorem mass_integrable (lam : Ioi (0 : ℝ)) : IntegrableOn (massDensity lam) fullDomain := by
  apply (full_weight_integrable.const_mul ((1 / 2 : ℝ) ^ (-(lam : ℝ) / 2))).mono'
    ((mass_continuousOn lam).aestronglyMeasurable fullDomain_measurable)
  filter_upwards [ae_restrict_mem fullDomain_measurable] with p hp
  rw [Real.norm_eq_abs, abs_of_pos (mass_pos lam hp)]
  have h := div_le_div_of_nonneg_right (model_bound lam hp) (sq_nonneg p.2)
  simpa only [massDensity, mul_one_div] using h

/-- The actual curvature is continuous throughout the upper half-plane. -/
theorem curvature_continuousOn (lam : Ioi (0 : ℝ)) :
    ContinuousOn (curvature lam) {z : ℂ | 0 < z.im} := by
  have hL : ContinuousOn (realLaplacian (model lam)) {z : ℂ | 0 < z.im} :=
    (second_regular (model lam) (model_c2 lam) 1 1).add
      (second_regular (model lam) (model_c2 lam) Complex.I Complex.I)
  exact ((Complex.continuous_im.pow 2).continuousOn.mul hL).add
    (continuousOn_const.mul (model_c2 lam).continuousOn)

/-- The literal model curvature density is strictly positive on the full domain. -/
theorem curve_pos (lam : Ioi (0 : ℝ)) {p : ℝ × ℝ} (hp : p ∈ fullDomain) : 0 < curveDensity lam p :=
  div_pos (curvature_pos lam (by simpa only [point_im] using fullDomain_height_pos hp))
    (sq_pos_of_pos (fullDomain_height_pos hp))

/-- The original pointwise curvature bound gives full curvature integrability. -/
theorem curve_integrable (lam : Ioi (0 : ℝ)) : IntegrableOn (curveDensity lam) fullDomain := by
  have hc : ContinuousOn (curveDensity lam) fullDomain := by
    intro p hp
    have hy := fullDomain_height_pos hp
    have hz : 0 < (point p.1 p.2).im := by simpa only [point_im] using hy
    have h := ((curvature_continuousOn lam).continuousAt
      (isOpen_upperHalfPlaneSet.mem_nhds hz)).comp (f := fun q : ℝ × ℝ => point q.1 q.2) chart_continuous.continuousAt
    exact (h.div ((continuous_snd.pow 2).continuousAt) (pow_ne_zero 2 hy.ne')).continuousWithinAt
  apply ((mass_integrable lam).const_mul (curvatureConstant lam)).mono'
    (hc.aestronglyMeasurable fullDomain_measurable)
  filter_upwards [ae_restrict_mem fullDomain_measurable] with p hp
  rw [Real.norm_eq_abs, abs_of_pos (curve_pos lam hp)]
  have h := div_le_div_of_nonneg_right
    (curvature_le_model lam (z := point p.1 p.2) (by simpa only [point_im] using fullDomain_height_pos hp)) (sq_nonneg p.2)
  simpa only [curveDensity, massDensity, mul_div_assoc] using h

/-- The original curvature density splits into actual planar Laplacian and hyperbolic mass. -/
theorem curveDensity_eq (lam : Ioi (0 : ℝ)) {p : ℝ × ℝ} (hp : p ∈ fullDomain) :
    curveDensity lam p = realLaplacian (model lam) (point p.1 p.2) + (lam : ℝ) * massDensity lam p := by
  have hy := fullDomain_height_pos hp
  unfold curveDensity curvature massDensity
  rw [point_im]
  field_simp [hy.ne']

/-- The actual planar model Laplacian is integrable on the untruncated modular domain. -/
theorem laplacian_integrable (lam : Ioi (0 : ℝ)) :
    IntegrableOn (fun p => realLaplacian (model lam) (point p.1 p.2)) fullDomain := by
  apply ((curve_integrable lam).sub ((mass_integrable lam).const_mul (lam : ℝ))).congr
  filter_upwards [ae_restrict_mem fullDomain_measurable] with p hp
  change curveDensity lam p - (lam : ℝ) * massDensity lam p = _
  rw [curveDensity_eq lam hp]
  ring

/-- A positive rectangle inside the literal modular domain gives positive domain area. -/
theorem fullDomain_volume_pos : 0 < volume fullDomain := by
  have hs : Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Icc (1 : ℝ) 2 ⊆ fullDomain := by
    intro p hp
    exact ⟨hp.1, (arcHeight_le_one hp.1).trans hp.2.1⟩
  have hv : (0 : ℝ≥0∞) < volume (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Icc (1 : ℝ) 2) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    norm_num [Real.volume_Icc]
  exact lt_of_lt_of_le hv (measure_mono hs)

/-- The actual finite amplitude mass is strictly positive. -/
theorem mass_integral_pos (lam : Ioi (0 : ℝ)) : 0 < ∫ p in fullDomain, massDensity lam p := by
  have hn : 0 ≤ᵐ[volume.restrict fullDomain] massDensity lam := by
    filter_upwards [ae_restrict_mem fullDomain_measurable] with p hp
    exact (mass_pos lam hp).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn (mass_integrable lam)]
  have he : Function.support (massDensity lam) ∩ fullDomain = fullDomain := by
    apply inter_eq_right.mpr
    intro p hp
    exact (mass_pos lam hp).ne'
  rw [he]
  exact fullDomain_volume_pos

/-- The original top-current integral has the proved uniform power envelope. -/
theorem top_bound (lam : Ioi (0 : ℝ)) {Y : ℝ} (hY : 0 < Y) :
    ‖∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt (model lam) Complex.I x Y‖ ≤
      (3 * (lam : ℝ) / 2) * Y ^ (-(lam : ℝ) / 2 - 1) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(1 / 2 : ℝ)) (b := 1 / 2) (fun x _ =>
      (show ‖currentAt (model lam) Complex.I x Y‖ ≤
        (3 * (lam : ℝ) / 2) * Y ^ (-(lam : ℝ) / 2 - 1) from by
          simpa only [Real.norm_eq_abs, currentAt] using model_vertical_le_height lam ⟨x, Y, hY⟩))
  norm_num at h ⊢
  exact h

/-- Original derivative control makes the actual top boundary current vanish at infinite height. -/
theorem top_limit (lam : Ioi (0 : ℝ)) :
    Tendsto (fun Y => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt (model lam) Complex.I x Y) atTop (𝓝 0) := by
  have hl : (0 : ℝ) < (lam : ℝ) := lam.2
  have ht : Tendsto (fun Y : ℝ => (3 * (lam : ℝ) / 2) * Y ^ (-(lam : ℝ) / 2 - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (lam : ℝ) / 2 + 1) (by positivity)).const_mul (3 * (lam : ℝ) / 2)
    simpa only [neg_add_rev, neg_div, mul_zero, show -(1 : ℝ) + -((lam : ℝ) / 2) = -((lam : ℝ) / 2) - 1 by ring] using h
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [eventually_gt_atTop (0 : ℝ), ht.eventually_lt_const heps] with Y hY hsmall
  simpa only [dist_zero_right] using lt_of_le_of_lt (top_bound lam hY) hsmall

/-- Actual Stokes and the proved cusp-current limit give zero full planar Laplacian integral. -/
theorem laplacian_integral_zero (lam : Ioi (0 : ℝ)) :
    (∫ p in fullDomain, realLaplacian (model lam) (point p.1 p.2)) = 0 := by
  have h := full_integral_tendsto (laplacian_integrable lam)
  have he : (fun Y => ∫ p in domain Y, realLaplacian (model lam) (point p.1 p.2)) =ᶠ[atTop]
      (fun Y => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt (model lam) Complex.I x Y) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    exact area_laplacian lam hY
  exact tendsto_nhds_unique h ((top_limit lam).congr' he.symm)

/-- The literal smooth positive scalar family has the exact full curvature budget for every lambda>0. -/
theorem curvature_budget (lam : Ioi (0 : ℝ)) :
    (∫ p in fullDomain, curveDensity lam p) = (lam : ℝ) * ∫ p in fullDomain, massDensity lam p := by
  calc
    _ = ∫ p in fullDomain, realLaplacian (model lam) (point p.1 p.2) + (lam : ℝ) * massDensity lam p := by
      apply setIntegral_congr_fun fullDomain_measurable
      intro p hp
      exact curveDensity_eq lam hp
    _ = _ := by
      rw [integral_add (laplacian_integrable lam) ((mass_integrable lam).const_mul (lam : ℝ)),
        laplacian_integral_zero, integral_const_mul, zero_add]

end
end GaloisForLFunctions.RHTower.SelbergEisensteinMass

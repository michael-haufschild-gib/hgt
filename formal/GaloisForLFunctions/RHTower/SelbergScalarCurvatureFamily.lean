import GaloisForLFunctions.RHTower.SelbergEisensteinMass

/-!
# Exact scalar curvature flexibility on the actual modular cell

For every positive lambda, the literal negative power of the original positive
Eisenstein series is smooth, modular, positive, and decays at the cusp. Its actual
curvature is positive, modular, integrable, and has total mass lambda times the
positive finite amplitude mass. Consequently this scalar family has no uniform
positive curvature-to-amplitude lower bound, in particular no quarter bound.

This excludes the stated scalar shortcut only. These functions are not claimed
to be Maass cusp eigenforms, nor to satisfy the original component equations,
weighted component mean zero, or exponential Maass cusp decay. Selberg's original
all-congruence assertion is not proved or refuted here.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergScalarCurvatureFamily
open SelbergPowerCurvature SelbergEisensteinBoundary SelbergEisensteinMass
  SelbergMaassMean SelbergMaassTraceEnergy SelbergMaassCellCurvature SelbergMaassFullCurvatureBudget
  SelbergMaassCuspTransport SelbergMaassCurvatureCovariance
open GaloisForLFunctions.HTGeometry.ComplexC2Laplacian (laplacian)
noncomputable section

private def complexModel (lam : Ioi (0 : ℝ)) (z : ℍ) : ℂ := (model lam (z : ℂ) : ℂ)

private theorem complex_chart_eq (lam : Ioi (0 : ℝ)) (z : ℍ) :
    (complexModel lam) ∘ ofComplex =ᶠ[𝓝 (z : ℂ)] (fun w => (model lam w : ℂ)) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, complexModel, ofComplex_apply_of_im_pos hw]

private theorem complex_model_smooth (lam : Ioi (0 : ℝ)) : IsRealSmoothUpperHalfPlane (complexModel lam) := by
  unfold IsRealSmoothUpperHalfPlane
  apply (Complex.ofRealCLM.contDiff.fun_comp_contDiffOn (model_c2 lam)).congr
  intro z hz
  simp only [Function.comp_apply, complexModel, ofComplex_apply_of_im_pos hz]
  rfl

private theorem laplacian_eventuallyEq {F G : ℂ → ℂ} {z : ℂ} (h : F =ᶠ[𝓝 z] G) :
    laplacian F z = laplacian G z := by
  have he (v : ℂ) : (fun w => fderiv ℝ F w v) =ᶠ[𝓝 z] (fun w => fderiv ℝ G w v) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with w hw
    rw [hw]
  unfold laplacian
  rw [(he 1).fderiv_eq, (he Complex.I).fderiv_eq]

private theorem complex_model_laplacian (lam : Ioi (0 : ℝ)) (z : ℍ) :
    positiveHyperbolicLaplacian (complexModel lam) z =
      (-(z.im ^ 2 * realLaplacian (model lam) (z : ℂ)) : ℝ) := by
  change -(z.im : ℂ) ^ 2 * laplacian ((complexModel lam) ∘ ofComplex) (z : ℂ) = _
  rw [laplacian_eventuallyEq (complex_chart_eq lam z),
    laplacian_ofReal ((model_c2 lam).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos))]
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow, neg_mul]

/-- The original scalar model's actual hyperbolic Laplacian is modular invariant. -/
theorem model_hyperbolic_laplacian_modular (lam : Ioi (0 : ℝ)) (A : SL2Z) (z : ℍ) :
    (A • z : ℍ).im ^ 2 * realLaplacian (model lam) ((A • z : ℍ) : ℂ) =
      z.im ^ 2 * realLaplacian (model lam) (z : ℂ) := by
  have h := positive_laplacian_pullback A (complexModel lam) (complex_model_smooth lam) z
  have he : (fun w : ℍ => complexModel lam (A • w)) = complexModel lam := by
    funext w
    simp only [complexModel, model_modular]
  rw [he, complex_model_laplacian, complex_model_laplacian] at h
  exact neg_injective (Complex.ofReal_injective h.symm)

/-- The actual positive curvature density respects every original modular transformation. -/
theorem curvature_modular (lam : Ioi (0 : ℝ)) (A : SL2Z) (z : ℍ) :
    curvature lam ((A • z : ℍ) : ℂ) = curvature lam (z : ℂ) := by
  unfold curvature
  simp only [UpperHalfPlane.coe_im, model_hyperbolic_laplacian_modular, model_modular]

private theorem point_self (z : ℍ) : point z.re z.im = (z : ℂ) := by
  apply Complex.ext <;> simp [point]

/-- The actual model's standard hyperbolic cell mass equals its literal planar weighted mass. -/
theorem cell_mass_eq (lam : Ioi (0 : ℝ)) :
    (∫ z : ℍ in fd, model lam (z : ℂ)) = ∫ p in fullDomain, massDensity lam p := by
  rw [← integral_height_sq_cell (massDensity lam)]
  apply setIntegral_congr_fun isClosed_fd.measurableSet
  intro z _
  change model lam (z : ℂ) = z.im ^ 2 * (model lam (point z.re z.im) / z.im ^ 2)
  rw [point_self]
  field_simp [z.im_pos.ne']

/-- The actual model's standard hyperbolic cell curvature equals the literal planar weighted integral. -/
theorem cell_curvature_eq (lam : Ioi (0 : ℝ)) :
    (∫ z : ℍ in fd, curvature lam (z : ℂ)) = ∫ p in fullDomain, curveDensity lam p := by
  rw [← integral_height_sq_cell (curveDensity lam)]
  apply setIntegral_congr_fun isClosed_fd.measurableSet
  intro z _
  change curvature lam (z : ℂ) = z.im ^ 2 * (curvature lam (point z.re z.im) / z.im ^ 2)
  rw [point_self]
  field_simp [z.im_pos.ne']

/-- The literal scalar family has positive finite standard-cell amplitude mass. -/
theorem cell_mass_pos (lam : Ioi (0 : ℝ)) : 0 < ∫ z : ℍ in fd, model lam (z : ℂ) := by
  rw [cell_mass_eq]
  exact mass_integral_pos lam

/-- The literal scalar family satisfies the same exact standard-cell total-curvature identity for every positive parameter. -/
theorem cell_curvature_budget (lam : Ioi (0 : ℝ)) :
    (∫ z : ℍ in fd, curvature lam (z : ℂ)) = (lam : ℝ) * ∫ z : ℍ in fd, model lam (z : ℂ) := by
  rw [cell_curvature_eq, cell_mass_eq, curvature_budget]

/-- The actual standard-cell mass is integrable, with no finite-mass premise. -/
theorem cell_mass_integrable (lam : Ioi (0 : ℝ)) :
    IntegrableOn (fun z : ℍ => model lam (z : ℂ)) fd :=
  Integrable.of_integral_ne_zero (cell_mass_pos lam).ne'

/-- The actual standard-cell curvature is integrable, with no finite-curvature premise. -/
theorem cell_curvature_integrable (lam : Ioi (0 : ℝ)) :
    IntegrableOn (fun z : ℍ => curvature lam (z : ℂ)) fd := by
  have hl : (0 : ℝ) < (lam : ℝ) := lam.2
  apply Integrable.of_integral_ne_zero
  rw [cell_curvature_budget]
  exact (mul_pos hl (cell_mass_pos lam)).ne'

/-- The actual scalar curvature-to-amplitude ratio can be every positive number. -/
theorem cell_curvature_mass_ratio (lam : Ioi (0 : ℝ)) :
    (∫ z : ℍ in fd, curvature lam (z : ℂ)) / (∫ z : ℍ in fd, model lam (z : ℂ)) = (lam : ℝ) := by
  rw [cell_curvature_budget]
  exact mul_div_cancel_right₀ _ (cell_mass_pos lam).ne'

/-- No positive constant uniformly bounds the actual scalar-family curvature by its amplitude mass from below. -/
theorem no_positive_uniform_comparison (c : Ioi (0 : ℝ)) :
    ¬ ∀ lam : Ioi (0 : ℝ), (c : ℝ) * (∫ z : ℍ in fd, model lam (z : ℂ)) ≤
      ∫ z : ℍ in fd, curvature lam (z : ℂ) := by
  intro h
  have hc : (0 : ℝ) < (c : ℝ) := c.2
  let lam : Ioi (0 : ℝ) := ⟨(c : ℝ) / 2, by change 0 < (c : ℝ) / 2; positivity⟩
  have hm := cell_mass_pos lam
  have hh := h lam
  rw [cell_curvature_budget] at hh
  change (c : ℝ) * (∫ z : ℍ in fd, model lam (z : ℂ)) ≤
    (c : ℝ) / 2 * (∫ z : ℍ in fd, model lam (z : ℂ)) at hh
  nlinarith

/-- The quarter comparison fails for the literal smooth modular positive scalar family. -/
theorem no_scalar_quarter_comparison :
    ¬ ∀ lam : Ioi (0 : ℝ), (1 / 4 : ℝ) * (∫ z : ℍ in fd, model lam (z : ℂ)) ≤
      ∫ z : ℍ in fd, curvature lam (z : ℂ) :=
  no_positive_uniform_comparison ⟨1 / 4, by norm_num⟩

end
end GaloisForLFunctions.RHTower.SelbergScalarCurvatureFamily

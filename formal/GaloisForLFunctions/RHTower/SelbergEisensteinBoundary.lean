import GaloisForLFunctions.RHTower.SelbergPowerCurvature
import GaloisForLFunctions.RHTower.SelbergModularPotentialGreen

/-!
# Actual modular boundary currents of the positive Eisenstein power model

Original S/T invariance extends to every modular matrix. Its actual Frechet
differential transforms with the reciprocal-square Mobius Jacobian. Translation
cancels side currents, and inversion cancels the oriented unit-circle currents.
The literal planar Green formula therefore leaves only the actual top current.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergEisensteinBoundary
open _root_.RHTower SelbergMaassMean SelbergMaassTraceEnergy SelbergPowerCurvature
  SelbergModularPotentialGreen SelbergModularDomainSlices
noncomputable section

private theorem point_self (z : ℂ) : point z.re z.im = z := by
  apply Complex.ext <;> simp [point]

private theorem point_halfPlane (z : ℍ) : point z.re z.im = (z : ℂ) := by
  rw [← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_im, point_self]

private theorem point_re (x y : ℝ) : (point x y).re = x := by simp [point]
private theorem point_im (x y : ℝ) : (point x y).im = y := by simp [point]

/-- The literal scalar model respects the original inversion on the half-plane. -/
theorem model_S (lam : Ioi (0 : ℝ)) (z : ℍ) :
    model lam ((S • z : ℍ) : ℂ) = model lam (z : ℂ) := by
  have h := model_invert lam ⟨z.re, z.im, z.im_pos⟩
  have hp : point (d4BMEisensteinInvertCoordinate ⟨z.re, z.im, z.im_pos⟩).x
      (d4BMEisensteinInvertCoordinate ⟨z.re, z.im, z.im_pos⟩).y = ((S • z : ℍ) : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    apply Complex.ext <;>
      simp only [point_re, point_im, d4BMEisensteinInvertCoordinate, Complex.inv_re, Complex.inv_im,
        Complex.neg_re, Complex.neg_im, Complex.normSq_apply,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, neg_div, neg_neg, sq, neg_mul_neg]
  simpa only [hp, point_halfPlane] using h

/-- The literal scalar model respects the original modular translation. -/
theorem model_T (lam : Ioi (0 : ℝ)) (z : ℍ) :
    model lam ((T • z : ℍ) : ℂ) = model lam (z : ℂ) := by
  have h := model_translate lam ⟨z.re, z.im, z.im_pos⟩
  have hp : point (z.re + 1) z.im = ((T • z : ℍ) : ℂ) := by
    apply Complex.ext <;>
      simp only [point_re, point_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
        ModularGroup.re_T_smul, ModularGroup.im_T_smul]
  simpa only [hp, point_halfPlane] using h

/-- The actual model is invariant under every integral modular matrix. -/
theorem model_modular (lam : Ioi (0 : ℝ)) (A : SL2Z) (z : ℍ) :
    model lam ((A • z : ℍ) : ℂ) = model lam (z : ℂ) := by
  have hA : A ∈ Subgroup.closure {S, T} := by simp [SpecialLinearGroup.SL2Z_generators]
  suffices ∀ z : ℍ, model lam ((A • z : ℍ) : ℂ) = model lam (z : ℂ) from this z
  induction hA using Subgroup.closure_induction with
  | mem g hg =>
    simp only [mem_insert_iff, mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact model_S lam
    · exact model_T lam
  | one => intro w; simp
  | mul g h _ _ ig ih => intro w; rw [mul_smul, ig, ih]
  | inv g _ ig => intro w; simpa using (ig (g⁻¹ • w)).symm

/-- The original model has the C² regularity required by actual planar Stokes. -/
theorem model_c2 (lam : Ioi (0 : ℝ)) : ContDiffOn ℝ 2 (model lam) {z : ℂ | 0 < z.im} :=
  (contDiffOn_infty.mp (model_contDiffOn lam)) 2

/-- Differentiating actual modular invariance transports the real model differential. -/
theorem current_modular (lam : Ioi (0 : ℝ)) (A : SL2Z) (z : ℍ) (v : ℂ) :
    dir v (model lam) (z : ℂ) = dir ((1 / (denom A z) ^ 2) * v) (model lam) ((A • z : ℍ) : ℂ) := by
  let G : ℂ → ℂ := fun w => ((A • ofComplex w : ℍ) : ℂ)
  have hG : HasFDerivAt G (UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z : ℂ)) (z : ℂ) :=
    (UpperHalfPlane.hasStrictFDerivAt_smul (A : GL (Fin 2) ℝ) z).hasFDerivAt
  have hF : DifferentiableAt ℝ (model lam) (G (z : ℂ)) := by
    simpa only [G, ofComplex_apply] using
      ((model_c2 lam).contDiffAt
        (isOpen_upperHalfPlaneSet.mem_nhds (A • z).im_pos)).differentiableAt (by norm_num)
  have he : (model lam) ∘ G =ᶠ[𝓝 (z : ℂ)] model lam := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    change model lam ((A • ofComplex w : ℍ) : ℂ) = model lam w
    rw [model_modular, ofComplex_apply_of_im_pos hw]
  have hc := hF.hasFDerivAt.comp (z : ℂ) hG
  have h := congrArg (fun L => L v) hc.fderiv
  rw [he.fderiv_eq] at h
  have hj : UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z : ℂ) v =
      (1 / (denom A z) ^ 2) * v := by
    simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, mul_comm]
  simpa only [ContinuousLinearMap.comp_apply, G, ofComplex_apply, hj, dir] using h

/-- Radial contraction of the actual model differential has its real coordinate decomposition. -/
theorem radial_components (lam : Ioi (0 : ℝ)) (z : ℍ) :
    dir (z : ℂ) (model lam) (z : ℂ) =
      z.re * dir 1 (model lam) (z : ℂ) + z.im * dir Complex.I (model lam) (z : ℂ) := by
  have he : (z : ℂ) = z.re • (1 : ℂ) + z.im • Complex.I := by
    change (z : ℂ) = (z : ℂ).re • (1 : ℂ) + (z : ℂ).im • Complex.I
    simpa only [Complex.real_smul, mul_one] using (z : ℂ).re_add_im.symm
  unfold dir
  rw [he, map_add, map_smul, map_smul]
  rfl

/-- Radial model currents reverse sign under the actual modular inversion. -/
theorem radial_inversion (lam : Ioi (0 : ℝ)) (z : ℍ) :
    dir (z : ℂ) (model lam) (z : ℂ) +
      dir ((S • z : ℍ) : ℂ) (model lam) ((S • z : ℍ) : ℂ) = 0 := by
  have h := current_modular lam S z (z : ℂ)
  have hv : (1 / (denom S z) ^ 2) * (z : ℂ) = -((S • z : ℍ) : ℂ) := by
    simp only [UpperHalfPlane.modular_S_smul]
    simp [denom, ModularGroup.S, inv_neg]
    field_simp
  rw [hv] at h
  unfold dir at h
  rw [map_neg] at h
  change dir (z : ℂ) (model lam) (z : ℂ) =
    -dir ((S • z : ℍ) : ℂ) (model lam) ((S • z : ℍ) : ℂ) at h
  linarith

/-- The original model's currents cancel on the paired vertical sides. -/
theorem side_cancellation (lam : Ioi (0 : ℝ)) {y : ℝ} (hy : 0 < y) :
    currentAt (model lam) 1 (1 / 2) y = currentAt (model lam) 1 (-(1 / 2)) y := by
  have h := current_modular lam T (ofComplex (point (-(1 / 2)) y)) 1
  rw [SelbergMaassTraceBoundary.translation_point _ hy,
    show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] at h
  have hp (x : ℝ) : 0 < (point x y).im := by simpa [point] using hy
  simpa [denom, ModularGroup.T, ofComplex_apply_of_im_pos (hp _), currentAt] using h.symm

/-- The two literal oriented unit-circle currents cancel for the actual model. -/
theorem arc_cancellation (lam : Ioi (0 : ℝ)) {x y : ℝ} (hy : 0 < y) (hxy : x ^ 2 + y ^ 2 = 1) :
    (x / y) * (currentAt (model lam) 1 (-x) y - currentAt (model lam) 1 x y) -
      currentAt (model lam) Complex.I (-x) y - currentAt (model lam) Complex.I x y = 0 := by
  have h := radial_inversion lam (ofComplex (point x y))
  rw [SelbergMaassTraceBoundary.inversion_on_unit_circle hy hxy, radial_components, radial_components] at h
  have hp (u : ℝ) : 0 < (point u y).im := by simpa [point] using hy
  have hr (u : ℝ) : (ofComplex (point u y)).re = u := by
    change (ofComplex (point u y) : ℂ).re = u
    rw [ofComplex_apply_of_im_pos (hp u)]
    simp [point]
  have hi (u : ℝ) : (ofComplex (point u y)).im = y := by
    change (ofComplex (point u y) : ℂ).im = y
    rw [ofComplex_apply_of_im_pos (hp u)]
    simp [point]
  rw [hr, hr, hi, hi, ofComplex_apply_of_im_pos (hp x), ofComplex_apply_of_im_pos (hp (-x))] at h
  unfold currentAt
  field_simp
  linear_combination -h

/-- Actual Stokes leaves only the model's top current on each truncated modular cell. -/
theorem area_laplacian (lam : Ioi (0 : ℝ)) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, realLaplacian (model lam) (point p.1 p.2)) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt (model lam) Complex.I x Y :=
  area_laplacian_eq_top (model lam) (model_c2 lam) (side_cancellation lam) (arc_cancellation lam) hY

end
end GaloisForLFunctions.RHTower.SelbergEisensteinBoundary

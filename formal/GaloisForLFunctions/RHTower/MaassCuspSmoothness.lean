import GaloisForLFunctions.HTGeometry.PlanarLocalEllipticRegularity
import GaloisForLFunctions.RHTower.MaassCuspAutomorphicCorrespondence

/-! Smoothness of the original C2 Maass eigenfunction follows from its elliptic equation. -/

namespace GaloisForLFunctions.RHTower
open UpperHalfPlane
open scoped ContDiff
noncomputable section

/-- The original Maass eigenfunction is smooth at every point of the upper half-plane. -/
theorem IsMaassEigenfunction.contDiffOn {eigenvalue : ℝ} {f : ℍ → ℂ}
    (hf : IsMaassEigenfunction eigenvalue f) :
    ContDiffOn ℝ ∞ (f ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  let Ω : TopologicalSpace.Opens ℂ := ⟨{z : ℂ | 0 < z.im}, isOpen_upperHalfPlaneSet⟩
  let V : ℂ → ℂ := fun z => -(eigenvalue : ℂ)/(z.im : ℂ)^2
  have hV : ContDiffOn ℝ ∞ V Ω := by
    intro z hz
    have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
    have hd : ContDiffAt ℝ ∞ (fun w : ℂ => (w.im : ℂ)^2) z :=
      ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).pow 2).contDiffAt
    simpa only [V,div_eq_mul_inv] using
      (contDiffAt_const.mul (hd.fun_inv (pow_ne_zero 2 hy))).contDiffWithinAt
  apply HTGeometry.PlanarElliptic.smooth_of_equation (Ω := Ω) hf.1 hV
  intro z hz
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have he := hf.2 ⟨z,hz⟩
  change -(z.im : ℂ)^2 *
    (HTGeometry.PlanarElliptic.dir 1 (HTGeometry.PlanarElliptic.dir 1 (f ∘ ofComplex)) z +
      HTGeometry.PlanarElliptic.dir Complex.I
        (HTGeometry.PlanarElliptic.dir Complex.I (f ∘ ofComplex)) z) =
    (eigenvalue : ℂ)*f ⟨z,hz⟩ at he
  change _ = (-(eigenvalue : ℂ)/(z.im : ℂ)^2) * f (ofComplex z)
  rw [ofComplex_apply_of_im_pos hz]
  apply mul_left_cancel₀ (pow_ne_zero 2 hy)
  field_simp
  linear_combination -he

/-- Cuspidal Maass forms inherit full smoothness without strengthening their definition. -/
theorem MaassCuspEigenform.contDiffOn {Γ : Subgroup SL2R} {eigenvalue : ℝ}
    (f : MaassCuspEigenform Γ eigenvalue) :
    ContDiffOn ℝ ∞ (f.1.1 ∘ ofComplex) {z : ℂ | 0 < z.im} :=
  f.property.2.1.contDiffOn

end
end GaloisForLFunctions.RHTower

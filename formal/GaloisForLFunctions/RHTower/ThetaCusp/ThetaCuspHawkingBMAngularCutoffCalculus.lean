import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalCoreCutoff

/-! Exact conjugation and complete cutoff product rule for the original hyperbolic angular operator. -/
open Complex Set Filter Topology
open scoped ContDiff ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Conjugation commutes with each original real coordinate derivative. -/
theorem coordDeriv_conj (f : (Fin 2 → ℝ) → ℂ) (i : Fin 2) (z : Fin 2 → ℝ) :
    coordDeriv i (fun w => conj (f w)) z = conj (coordDeriv i f z) := by
  change fderiv ℝ (Complex.conjCLE ∘ f) z (Pi.single i 1) = _
  rw [Complex.conjCLE.comp_fderiv]
  rfl

/-- The complete hyperbolic angular Laplacian commutes with complex conjugation. -/
theorem hyperbolicLaplacian_conj (f : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℝ) :
    hyperbolicLaplacian (fun w => conj (f w)) z = conj (hyperbolicLaplacian f z) := by
  have he (i : Fin 2) : coordDeriv i (fun w => conj (f w)) = fun w => conj (coordDeriv i f w) :=
    funext (coordDeriv_conj f i)
  simp only [hyperbolicLaplacian,he,coordDeriv_conj,map_mul,map_add,map_pow,Complex.conj_ofReal]

end
end RHTower.D4BMAngularSeries

namespace RHTower.D4BMJointWave
open D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private def heightProfile (h : ℝ → ℝ) (z : Fin 2 → ℝ) : ℂ := h (z 1)

private theorem heightProfile_deriv (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (i : Fin 2) (z : Fin 2 → ℝ) :
    coordDeriv i (heightProfile h) z = ((deriv h (z 1):ℝ):ℂ)*(((Pi.single i (1:ℝ) : Fin 2 → ℝ) 1):ℂ) := by
  have hd := (hh.differentiable (by simp)).differentiableAt.hasDerivAt (x := z 1)
  let Y : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  have he := Complex.ofRealCLM.hasFDerivAt.comp z (hd.hasFDerivAt.comp z Y.hasFDerivAt)
  change fderiv ℝ (Complex.ofRealCLM ∘ h ∘ Y) z (Pi.single i 1) = _
  rw [he.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    Complex.ofRealCLM_apply,ContinuousLinearMap.proj_apply,Y,smul_eq_mul,Complex.ofReal_mul]
  ring

private theorem heightProfile_jet (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (z : Fin 2 → ℝ) :
    (ofField (heightProfile h) z).first 0 = 0 ∧
    (ofField (heightProfile h) z).first 1 = ((deriv h (z 1):ℝ):ℂ) ∧
    (ofField (heightProfile h) z).second 0 0 = 0 ∧
    (ofField (heightProfile h) z).second 1 1 = ((deriv (deriv h) (z 1):ℝ):ℂ) := by
  have h0 : coordDeriv 0 (heightProfile h) = fun _ => (0:ℂ) := by
    funext w
    simp only [heightProfile_deriv h hh,Pi.single_eq_of_ne (by decide : (1:Fin 2) ≠ 0),
      Complex.ofReal_zero,mul_zero]
  have h1 : coordDeriv 1 (heightProfile h) = heightProfile (deriv h) := by
    funext w
    simp only [heightProfile_deriv h hh,Pi.single_eq_same,Complex.ofReal_one,mul_one,heightProfile]
  have hd := (contDiff_infty_iff_deriv.mp hh).2
  change coordDeriv 0 (heightProfile h) z = 0 ∧ _
  refine ⟨congrFun h0 z,congrFun h1 z,?_,?_⟩
  · change coordDeriv 0 (coordDeriv 0 (heightProfile h)) z = 0
    rw [h0]
    change fderiv ℝ (fun _ : Fin 2 → ℝ => (0:ℂ)) z (Pi.single 0 1) = 0
    rw [(hasFDerivAt_const (0:ℂ) z).fderiv]
    rfl
  · change coordDeriv 1 (coordDeriv 1 (heightProfile h)) z = _
    rw [h1,heightProfile_deriv _ hd]
    simp only [Pi.single_eq_same,Complex.ofReal_one,mul_one]

/-- Both derivative terms of a height cutoff remain in the original angular differential expression. -/
theorem hyperbolicLaplacian_height_mul (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (f : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℝ) (hf : ContDiffAt ℝ 2 f z) :
    hyperbolicLaplacian (fun w => (h (w 1):ℂ)*f w) z =
      (h (z 1):ℂ)*hyperbolicLaplacian f z+
      2*(z 1:ℂ)^(2 : ℕ)*((deriv h (z 1):ℝ):ℂ)*coordDeriv 1 f z+
      (z 1:ℂ)^(2 : ℕ)*((deriv (deriv h) (z 1):ℝ):ℂ)*f z := by
  have hH : ContDiffAt ℝ 2 (heightProfile h) z := by
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (((contDiff_infty.mp hh) 2).contDiffAt.comp z
        (show (Fin 2 → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj 1).contDiff.contDiffAt)
  have hj := heightProfile_jet h hh z
  change (z 1:ℂ)^(2 : ℕ)*((ofField (fun w => heightProfile h w*f w) z).second 0 0+
      (ofField (fun w => heightProfile h w*f w) z).second 1 1) = _
  rw [ofField_mul hH hf]
  simp only [ScalarTwoJet.mul,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2]
  simp only [ofField,heightProfile,hyperbolicLaplacian]
  ring

end
end RHTower.D4BMJointWave

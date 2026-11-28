import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Tactic

/-! # Midpoint of an operator-norm circuit tube in a single angular chart -/

open Matrix Finset Complex
open scoped Matrix.Norms.L2Operator ComplexConjugate NNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where

/-- The distance of a unitary from the identity is attained on a single unitary eigenline. -/
private theorem extremal_line (W : unitary (Mat I)) :
    ∃ z : ℂ, ‖z‖=1 ∧ ‖1-z‖=‖1-W.val‖ ∧ ∃ v : I → ℂ, v≠0 ∧ W.val *ᵥ v=z • v := by
  obtain ⟨μ,hmem,hnorm⟩ := spectrum.exists_nnnorm_eq_spectralRadius (1-W.val)
  rw [IsStarNormal.spectralRadius_eq_nnnorm] at hnorm
  rw [←Matrix.spectrum_toLin'] at hmem
  obtain ⟨v,hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hmem).exists_hasEigenvector
  have hact := hv.apply_eq_smul
  rw [Matrix.toLin'_apply,sub_mulVec,one_mulVec] at hact
  let z := 1-μ
  have he : W.val *ᵥ v=z • v := by rw [show z=1-μ from rfl,sub_smul,one_smul,←hact,sub_sub_cancel]
  have hsv : Module.End.HasEigenvector W.val.toLin' z v := ⟨Module.End.mem_eigenspace_iff.mpr he,hv.2⟩
  have hm := (Module.End.hasEigenvalue_of_hasEigenvector hsv).mem_spectrum
  rw [Matrix.spectrum_toLin'] at hm
  refine ⟨z,mem_sphere_zero_iff_norm.mp (Unitary.spectrum_subset_circle W hm),?_,v,hv.2,he⟩
  rw [show 1-z=μ from sub_sub_cancel ..]
  exact congrArg (fun x : ℝ≥0 => (x:ℝ)) (ENNReal.coe_inj.mp hnorm)

omit [Nonempty I] in
/-- The endpoint error tested on an eigenvector is a weighted sum of scalar chords. -/
private theorem chord_sum (W : unitary (Mat I)) (u : I → ℂ) {z : ℂ} {v : I → ℂ}
    (he : W.val *ᵥ v=z • v) {ε : ℝ} (h : ‖diagonal u-W.val‖≤ε) :
    (∑ i, ‖u i-z‖^2*‖v i‖^2) ≤ ε^2*∑ i, ‖v i‖^2 := by
  let a := WithLp.toLp 2 v
  have hvec : (diagonal u-W.val) *ᵥ v=fun i => (u i-z)*v i := by
    rw [sub_mulVec,he]
    funext i
    simp only [Pi.sub_apply,mulVec_diagonal,Pi.smul_apply,smul_eq_mul,sub_mul]
  have hh := ((diagonal u-W.val).l2_opNorm_mulVec a).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  change ‖WithLp.toLp 2 ((diagonal u-W.val) *ᵥ v)‖^2≤(ε*‖a‖)^2 at hs
  rw [hvec,mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq] at hs
  simpa only [WithLp.ofLp_toLp,norm_mul,mul_pow,a] using hs

/-- For conjugate diagonal endpoints in the closed right half-plane, squared
operator error at their midpoint is bounded by the mean squared endpoint error. -/
theorem midpoint_square (W : unitary (Mat I)) (u : I → ℂ) (hu : ∀ i, ‖u i‖=1)
    (hr : ∀ i, 0≤(u i).re) {p m : ℝ} (hcut : p^2+m^2<4)
    (hp : ‖diagonal u-W.val‖≤p) (hm : ‖diagonal (fun i => conj (u i))-W.val‖≤m) :
    2*‖1-W.val‖^2≤p^2+m^2 := by
  classical
  obtain ⟨z,hz,hd,v,hv,he⟩ := extremal_line W
  by_contra! hlarge
  rw [←hd] at hlarge
  have hsq := hlarge
  rw [Complex.sq_norm,Complex.normSq_sub] at hsq
  simp only [map_one,Complex.normSq_eq_norm_sq,hz,one_pow,one_mul,Complex.conj_re] at hsq
  have hbad (i : I) : p^2+m^2 < ‖u i-z‖^2+‖conj (u i)-z‖^2 := by
    have hu' := (le_abs_self (u i).re).trans ((Complex.abs_re_le_norm _).trans_eq (hu i))
    have hreal : (u i).re*z.re<1-(p^2+m^2)/4 := by
      by_cases hz' : 0≤z.re
      · have hr' := mul_le_mul_of_nonneg_right hu' hz'
        linarith only [hr',hsq]
      · have hr' := mul_nonpos_of_nonneg_of_nonpos (hr i) (le_of_not_ge hz')
        linarith only [hr',hcut]
    rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_sub,Complex.normSq_sub,Complex.normSq_conj]
    simp only [Complex.normSq_eq_norm_sq,hz,hu,one_pow,Complex.mul_re,Complex.conj_im,Complex.conj_re]
    linarith only [hreal]
  have hp' := chord_sum W u he hp
  have hm' := chord_sum W (fun i => conj (u i)) he hm
  have hv' : ∃ i, v i≠0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨j,hj⟩ := hv'
  have hsum : (∑ i, (p^2+m^2)*‖v i‖^2) < ∑ i, (‖u i-z‖^2+‖conj (u i)-z‖^2)*‖v i‖^2 := by
    apply sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_right (hbad i).le (sq_nonneg _))
    exact ⟨j,mem_univ j,mul_lt_mul_of_pos_right (hbad j) (sq_pos_of_pos (norm_pos_iff.mpr hj))⟩
  simp only [add_mul,sum_add_distrib,←mul_sum] at hsum
  linarith only [hp',hm',hsum]

/-- A common error below the semicircle threshold is preserved by the midpoint. -/
theorem midpoint_fit (W : unitary (Mat I)) (u : I → ℂ) (hu : ∀ i, ‖u i‖=1)
    (hr : ∀ i, 0≤(u i).re) {ε : ℝ} (hε : ε^2<2)
    (hp : ‖diagonal u-W.val‖≤ε) (hm : ‖diagonal (fun i => conj (u i))-W.val‖≤ε) :
    ‖1-W.val‖≤ε := by
  have h := midpoint_square W u hu hr (by linarith only [hε]) hp hm
  exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hp)).mp (by linarith only [h])

#print axioms midpoint_square
#print axioms midpoint_fit
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes

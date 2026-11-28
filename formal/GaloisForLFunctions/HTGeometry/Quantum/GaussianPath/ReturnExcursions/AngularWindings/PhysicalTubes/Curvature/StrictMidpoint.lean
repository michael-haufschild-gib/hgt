import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Curvature.Equality
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Curvature.UniquePhase

/-! # Strict projective interpolation from one stationary coordinate -/

open Matrix Complex Set
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open private extremal_line from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.UnitaryMidpoint
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where

private theorem eigen_mem {Y : Mat I} {w : ℂ} {b : I → ℂ} (hb : b≠0) (h : Y *ᵥ b=w • b) :
    w∈spectrum ℂ Y := by
  rw [←Matrix.spectrum_toLin']
  have hh : Module.End.HasEigenvector Y.toLin' w b := ⟨Module.End.mem_eigenspace_iff.mpr h,hb⟩
  exact (Module.End.hasEigenvalue_of_hasEigenvector hh).mem_spectrum

private theorem scalar_gap {W : unitary (Mat I)} {c : ℂ} (hc : ‖c‖=1) {ε : ℝ}
    (h : ∀ w∈spectrum ℂ W.val, ‖c-w‖<ε) : ‖c • (1 : Mat I)-W.val‖<ε := by
  have hc₀ : c≠0 := norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero)
  have hi : ‖c⁻¹‖=1 := by rw [norm_inv,hc,inv_one]
  have hu : c⁻¹∈unitary ℂ := by
    have hh : star c⁻¹*c⁻¹=1 := by rw [Complex.star_def,Complex.conj_mul',hi]; norm_num
    exact Unitary.mem_iff.mpr ⟨hh,(mul_comm ..).trans hh⟩
  let Y : unitary (Mat I) := ⟨c⁻¹ • W.val,Unitary.smul_mem_of_mem hu W.2⟩
  obtain ⟨w,_,hd,b,hb,he⟩ := extremal_line Y
  change (c⁻¹ • W.val) *ᵥ b=w • b at he
  rw [Matrix.smul_mulVec] at he
  have hev := congrArg (fun a : I → ℂ => c • a) he
  simp only [smul_smul,mul_inv_cancel₀ hc₀,one_smul] at hev
  have hh := h (c*w) (eigen_mem hb hev)
  rw [show c-c*w=c*(1-w) by ring,norm_mul,hc,one_mul,hd] at hh
  have hW : c • Y.val=W.val := by change c • (c⁻¹ • W.val)=_; rw [smul_smul,mul_inv_cancel₀ hc₀,one_smul]
  rwa [←hW,←smul_sub,norm_smul,hc,one_mul]

/-- For equal positive endpoint tolerances, the midpoint fit is strictly
better after optimizing phase if at most one coordinate is stationary. -/
theorem strict_projective_midpoint (W : unitary (Mat I)) (u : I → ℂ) (hu : ∀ i, ‖u i‖=1)
    (hr : ∀ i, 0≤(u i).re) (hsingle : ∀ i j, (u i).re=1 → (u j).re=1 → i=j)
    {ε : ℝ} (hε : 0<ε) (hcut : ε^2<2) (hp : ‖diagonal u-W.val‖≤ε)
    (hm : ‖diagonal (fun i => conj (u i))-W.val‖≤ε) :
    ∃ c : ℂ, ‖c‖=1 ∧ ‖c • (1 : Mat I)-W.val‖<ε := by
  have hmid := midpoint_fit W u hu hr hcut hp hm
  rcases hmid.lt_or_eq with hmid|hmid
  · exact ⟨1,norm_one,by simpa only [one_smul] using hmid⟩
  obtain ⟨z,hz,hd,v,hv,he⟩ := extremal_line W
  obtain ⟨c,hc,hf⟩ := rotate_unique_phase (spectrum ℂ W.val) (Matrix.finite_spectrum _) hz hε hcut
    (hd.trans hmid) (by
      intro w hw hne
      have hw₁ := mem_sphere_zero_iff_norm.mp (Unitary.spectrum_subset_circle W hw)
      rw [←Matrix.spectrum_toLin'] at hw
      obtain ⟨b,hb⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hw).exists_hasEigenvector
      have hbw := hb.apply_eq_smul
      rw [Matrix.toLin'_apply] at hbw
      have hs : 1-w∈spectrum ℂ (1-W.val) := eigen_mem hb.2 (by
        rw [sub_mulVec,one_mulVec,hbw,sub_smul,one_smul])
      apply ((spectrum.norm_le_norm_of_mem hs).trans_eq hmid).lt_of_ne
      intro hdw
      exact hne (active_phase_unique hu hsingle hcut hp hm hw₁ hz hdw (hd.trans hmid) hb.2 hv hbw he))
  exact ⟨c,hc,scalar_gap hc hf⟩

#print axioms strict_projective_midpoint
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes

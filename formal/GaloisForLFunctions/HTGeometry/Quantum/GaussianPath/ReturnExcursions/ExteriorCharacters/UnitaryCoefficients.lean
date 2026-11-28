import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.ArcCoefficients
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! # Simultaneous exterior-character bounds from operator error -/

open Matrix Polynomial
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where

private theorem chord_bound (Y : unitary (Mat I)) {z : ℂ} (h : z∈spectrum ℂ Y.val) :
    ‖1-z‖≤‖1-Y.val‖ := by
  rw [←Matrix.spectrum_toLin'] at h
  obtain ⟨u,hu⟩ := (Module.End.HasEigenvalue.of_mem_spectrum h).exists_hasEigenvector
  have hv := hu.apply_eq_smul
  rw [Matrix.toLin'_apply] at hv
  have hb : Module.End.HasEigenvector (1-Y.val).toLin' (1-z) u := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_,hu.2⟩
    rw [Matrix.toLin'_apply,sub_mulVec,one_mulVec,hv,sub_smul,one_smul]
  have hm := (Module.End.hasEigenvalue_of_hasEigenvector hb).mem_spectrum
  rw [Matrix.spectrum_toLin'] at hm
  exact spectrum.norm_le_norm_of_mem hm

private theorem unitary_floor (Y : unitary (Mat I)) {e : ℝ} (hfit : ‖1-Y.val‖≤e)
    (hc : 0≤1-e^2/2) (j : ℕ) (hj : j≤Fintype.card I) :
    ((Fintype.card I).choose j:ℝ)*(1-e^2/2)^(Fintype.card I-j)≤‖Y.val.charpoly.coeff j‖ := by
  have hroot : Y.val.charpoly.rootSet ℂ ⊆ {z | 1-e^2/2≤z.re} := by
    intro z hz
    have hm : z∈spectrum ℂ Y.val := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
      (by simpa only [IsRoot.def,coe_aeval_eq_eval] using (mem_rootSet.mp hz).2)
    have hz₁ := mem_sphere_zero_iff_norm.mp (Unitary.spectrum_subset_circle Y hm)
    have hs := pow_le_pow_left₀ (norm_nonneg _) ((chord_bound Y hm).trans hfit) 2
    rw [Complex.sq_norm,Complex.normSq_sub] at hs
    simp only [map_one,Complex.normSq_eq_norm_sq,hz₁,one_pow,one_mul,Complex.conj_re] at hs
    change 1-e^2/2≤z.re
    linarith only [hs]
  have h := coefficient_floor Y.val.charpoly hc hroot j (Y.val.charpoly_natDegree_eq_dim ▸ hj)
  simpa only [Y.val.charpoly_natDegree_eq_dim,Y.val.charpoly_monic.leadingCoeff,norm_one,mul_one] using h

omit [Nonempty I] in
private theorem inverse_coeff (Y : unitary (Mat I)) (j : ℕ) (hj : j≤Fintype.card I) :
    ‖(Y⁻¹).val.charpoly.coeff j‖=‖Y.val.charpoly.coeff (Fintype.card I-j)‖ := by
  have hi : Y.val⁻¹=(Y⁻¹).val := Matrix.inv_eq_left_inv (Unitary.mem_iff.mp Y.2).1
  have hu : IsUnit Y.val := (Unitary.toUnits Y).isUnit
  have hd : ‖Y.val.det‖=1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary Y.2)
  rw [←hi,Y.val.charpoly_inv hu,←Y.val.reverse_charpoly]
  rw [show (-1 : ℂ[X])^Fintype.card I=C ((-1 : ℂ)^Fintype.card I) by simp,
    ←map_mul,coeff_C_mul,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,
    Ring.inverse_eq_inv,norm_inv,hd,inv_one,mul_one,one_mul,coeff_reverse]
  simp [Y.val.charpoly_natDegree_eq_dim,hj]

/-- A single operator-norm fit constrains every exterior degree. Taking the
adjoint exchanges complementary degrees without changing the spectral arc. -/
theorem unitary_character_floor (Y : unitary (Mat I)) {e : ℝ} (hfit : ‖1-Y.val‖≤e)
    (hc : 0≤1-e^2/2) (q : ℕ) (hq : q≤Fintype.card I) :
    ((Fintype.card I).choose q:ℝ)*(1-e^2/2)^min q (Fintype.card I-q)
      ≤ ‖Y.val.charpoly.coeff (Fintype.card I-q)‖ := by
  let d := Fintype.card I
  by_cases h : q≤d-q
  · rw [min_eq_left h]
    have hh := unitary_floor Y hfit hc (d-q) (Nat.sub_le ..)
    simpa only [d,Nat.sub_sub_self hq,Nat.choose_symm hq] using hh
  · rw [min_eq_right (le_of_not_ge h)]
    have hstar : ‖1-(Y⁻¹).val‖=‖1-Y.val‖ := by
      change ‖1-star Y.val‖=_
      simpa only [star_sub,star_one] using norm_star (1-Y.val)
    exact (unitary_floor Y⁻¹ (hstar.trans_le hfit) hc q hq).trans_eq (inverse_coeff Y q hq)

#print axioms unitary_character_floor
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters

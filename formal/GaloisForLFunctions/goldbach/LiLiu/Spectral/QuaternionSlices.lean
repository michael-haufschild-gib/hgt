import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.Complex.Module

/-! # Complex slices cover quaternion space -/

namespace GaloisForLFunctions.Goldbach.LiLiu
noncomputable section

/-- Normalize the pure imaginary part to obtain a square root of −1.
For real quaternions the standard complex slice suffices. -/
theorem quaternion_mem_complex_slice (q : ℍ) : ∃ (f : ℂ →ₐ[ℝ] ℍ) (z : ℂ), f z=q := by
  by_cases h : q.im=0
  · refine ⟨Quaternion.ofComplex,(q.re:ℂ),?_⟩
    change (q.re : ℍ)=q
    simpa only [h,add_zero] using Quaternion.re_add_im q
  let r := ‖q.im‖
  have hr : r ≠ 0 := norm_ne_zero_iff.mpr h
  let J := r⁻¹ • q.im
  have hJ : J*J=-1 := by
    have hsq : q.im*q.im = -(algebraMap ℝ ℍ (r*r)) := by
      simpa only [← sq,Quaternion.normSq_eq_norm_mul_self,r] using Quaternion.im_sq q
    rw [show J*J=(r⁻¹*r⁻¹) • (q.im*q.im) by exact smul_mul_smul_comm ..,hsq,smul_neg,
      Algebra.algebraMap_eq_smul_one (r*r),smul_smul]
    simp [hr,mul_mul_mul_comm]
  refine ⟨Complex.liftAux J hJ,⟨q.re,r⟩,?_⟩
  change (q.re : ℍ) + r • (r⁻¹ • q.im)=q
  rw [smul_smul,mul_inv_cancel₀ hr,one_smul,Quaternion.re_add_im]

#print axioms quaternion_mem_complex_slice
end
end GaloisForLFunctions.Goldbach.LiLiu

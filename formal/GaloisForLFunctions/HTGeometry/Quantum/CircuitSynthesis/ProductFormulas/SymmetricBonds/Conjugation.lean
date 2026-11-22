import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.InteractionPicture

/-! # Linear approximation to a conjugated observable with a double-commutator remainder -/
open NormedSpace
namespace GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
noncomputable section
open LocalPatches
variable {R : Type*} [CStarAlgebra R]
local instance : NormedAlgebra ℚ R := .restrictScalars ℚ ℂ R

def conjugate (a x : R) (s : ℝ) := exp (s • (-a))*x*exp (s • a)

theorem flow_inverse (a : R) (s : ℝ) : exp (s • a)*exp (s • (-a))=1 := by
  rw [smul_neg,←exp_add_of_commute (Commute.refl (s • a)).neg_right,add_neg_cancel,exp_zero]

theorem flow_unitary (a : R) (ha : a ∈ skewAdjoint R) (s : ℝ) : exp (s • a) ∈ unitary R :=
  exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s ha)

private theorem conjugate_deriv (a x : R) (s : ℝ) :
    HasDerivAt (conjugate a x) (conjugate a (bracketStep a x) s) s := by
  have h := ((hasDerivAt_exp_smul_const (-a) s).mul_const x).fun_mul (hasDerivAt_exp_smul_const' a s)
  change HasDerivAt (fun r : ℝ => exp (r • (-a))*x*exp (r • a)) (exp (s • (-a))*(x*a-a*x)*exp (s • a)) s
  convert h using 1
  noncomm_ring

/-- Subtracting the linear Heisenberg term leaves an error controlled at
all positive times by the second commutator, even for a large generator. -/
theorem conjugate_remainder (a x : R) (ha : a ∈ skewAdjoint R) (t : ℝ) (ht : 0≤t) :
    ‖conjugate a x t-x-t • bracketStep a x‖ ≤ t^2*‖bracketStep a (bracketStep a x)‖ := by
  let c := bracketStep a x
  let f (s : ℝ) := conjugate a x s-x-s • c
  have hd (s : ℝ) : HasDerivAt f (conjugate a c s-c) s := by
    simpa only [f,one_smul] using ((conjugate_deriv a x s).sub_const x).sub ((hasDerivAt_id s).smul_const c)
  have hb (s : ℝ) (hs : s∈Set.Ico 0 t) : ‖conjugate a c s-c‖ ≤ t*‖bracketStep a c‖ := by
    have hcancel : exp (s • (-a))*exp (s • a)=1 := by simpa only [neg_neg] using flow_inverse (-a) s
    have he : conjugate a c s-c=exp (s • (-a))*(c*exp (s • a)-exp (s • a)*c) := by
      rw [mul_sub,←mul_assoc,←mul_assoc,hcancel,one_mul]; rfl
    rw [he,CStarRing.norm_mem_unitary_mul _ (flow_unitary _ ((skewAdjoint R).neg_mem ha) _),norm_sub_rev]
    have h := norm_exp_mul_sub_mul_exp_le_commutator a c ha s hs.1
    rw [norm_sub_rev (a*c),mul_comm] at h
    exact h.trans (mul_le_mul_of_nonneg_right hs.2.le (norm_nonneg _))
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (fun s _ => (hd s).hasDerivWithinAt) hb t ⟨ht,le_rfl⟩
  have hzero : f 0=0 := by simp [f,conjugate]
  rw [hzero,sub_zero,sub_zero] at h
  exact h.trans_eq (by change t*‖bracketStep a c‖*t=t^2*‖bracketStep a c‖; ring)

end
end GaloisForLFunctions.HTGeometry.BondProducts.Symmetric

import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.Intertwiner

/-! # A second-order estimate for compressed unitary evolution -/

open NormedSpace Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit.TangentCuts
noncomputable section
variable {A : Type*} [CStarAlgebra A]
local instance compressionRationalAlgebra : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

private theorem positive_remainder (a L R : A) (ha : a∈skewAdjoint A) (t : ℝ) (ht : 0≤t) :
    ‖L*exp (t • a)*R-L*R-t • (L*a*R)‖≤t^2*(‖L*a‖*‖a*R‖) := by
  let F (s : ℝ) := L*exp (s • a)*R-s • (L*a*R)
  let G (s : ℝ) := L*a*exp (s • a)*R
  let C := ‖L*a‖*‖a*R‖
  have hd (s : ℝ) : HasDerivAt G ((L*a*exp (s • a))*(a*R)) s := by
    have h := ((hasDerivAt_exp_smul_const a s).const_mul (L*a)).mul_const R
    simpa only [G,mul_assoc] using h
  have hbound (s : ℝ) : ‖(L*a*exp (s • a))*(a*R)‖≤C := by
    apply (norm_mul_le _ _).trans_eq
    rw [CStarRing.norm_mul_mem_unitary _ (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s ha))]
  have drift (s : ℝ) (hs : 0≤s) : ‖G s-L*a*R‖≤C*s := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a:=0) (b:=s)
      (fun r _ => (hd r).hasDerivWithinAt) (fun r _ => hbound r) s ⟨hs,le_rfl⟩
    simpa only [G,zero_smul,exp_zero,mul_one,sub_zero] using h
  have hf (s : ℝ) : HasDerivAt F (G s-L*a*R) s := by
    have h := ((hasDerivAt_exp_smul_const' a s).const_mul L).mul_const R
    have lin : HasDerivAt (fun r : ℝ => r • (L*a*R)) (L*a*R) s := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id s).smul_const (L*a*R)
    simpa only [F,G,mul_assoc] using h.sub lin
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a:=0) (b:=t)
    (fun s _ => (hf s).hasDerivWithinAt) (fun s hs => (drift s hs.1).trans
      (mul_le_mul_of_nonneg_left hs.2.le (mul_nonneg (norm_nonneg _) (norm_nonneg _)))) t ⟨ht,le_rfl⟩
  simp only [F,zero_smul,exp_zero,mul_one,sub_zero] at h
  rw [sub_sub_right_comm]
  exact h.trans_eq (by dsimp only [C]; ring)

/-- Compression by L and R controls the quadratic remainder by the two
endpoint norms. Centering an energy before projecting onto a basis vector
makes their product the energy variance in that vector. -/
theorem compressed_remainder (a L R : A) (ha : a∈skewAdjoint A) (t : ℝ) :
    ‖L*exp (t • a)*R-L*R-t • (L*a*R)‖≤t^2*(‖L*a‖*‖a*R‖) := by
  rcases le_total 0 t with ht|ht
  · exact positive_remainder a L R ha t ht
  · simpa only [neg_smul,smul_neg,neg_neg,mul_neg,neg_mul,norm_neg,neg_sq] using
      positive_remainder (-a) L R ((skewAdjoint A).neg_mem ha) (-t) (neg_nonneg.mpr ht)

#print axioms compressed_remainder
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit.TangentCuts

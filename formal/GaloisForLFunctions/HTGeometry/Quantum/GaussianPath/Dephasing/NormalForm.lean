import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.Intertwiner

/-! # First-order dephasing with an explicit inverse-time error -/
open NormedSpace
namespace GaloisForLFunctions.HTGeometry.Dephasing
noncomputable section
variable {A : Type*} [CStarAlgebra A]

private abbrev evolve (H : A) (t : ℝ) := exp (t • ((-Complex.I) • H))

private theorem unitary_evolve (H : A) (hH : IsSelfAdjoint H) (t : ℝ) : evolve H t∈unitary A := by
  letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  apply exp_mem_unitary_of_mem_skewAdjoint
  apply skewAdjoint.smul_mem
  rw [skewAdjoint.mem_iff,star_smul,hH.star_eq]
  simp

/-- If [H,X]=Z−D, then 1−hX intertwines H+hZ and H+hD up to second order.
For a spectral diagonal D this removes the off-diagonal part of the field. -/
theorem field_evolution_bound (H Z D X : A) (hH : IsSelfAdjoint H)
    (hZ : IsSelfAdjoint Z) (hD : IsSelfAdjoint D) (hx : H*X-X*H=Z-D) (h T : ℝ) :
    ‖evolve (H+h • Z) T-evolve (H+h • D) T‖≤
      2*|h| * ‖X‖+|T| * h^2*‖X*D-Z*X‖ := by
  let K := H+h • Z
  let L := H+h • D
  let B := 1-h • X
  have herm (Y : A) (hy : IsSelfAdjoint Y) : IsSelfAdjoint (H+h • Y) := by
    change star (H+h • Y)=H+h • Y
    rw [star_add,star_smul,hH.star_eq,hy.star_eq,star_trivial]
  have hdef : K*B-B*L=h^2 • (X*D-Z*X) := by
    calc
      K*B-B*L=h • ((Z-D)-(H*X-X*H))+h^2 • (X*D-Z*X) := by
        simp only [K,L,B,mul_sub,sub_mul,add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,
          mul_smul_comm,smul_sub,smul_add,smul_smul,sq]
        abel
      _ = _ := by rw [hx,sub_self,smul_zero,zero_add]
  let U := evolve K T
  let V := evolve L T
  have hnorm : ‖U*X-X*V‖≤2*‖X‖ := by
    calc _ ≤ ‖U*X‖+‖X*V‖ := norm_sub_le _ _
         _ = _ := by rw [CStarRing.norm_mem_unitary_mul _ (unitary_evolve K (herm Z hZ) T),
                          CStarRing.norm_mul_mem_unitary _ (unitary_evolve L (herm D hD) T),two_mul]
  have hsplit : U-V=(U*B-B*V)+h • (U*X-X*V) := by
    simp only [B,mul_sub,sub_mul,mul_one,one_mul,mul_smul_comm,smul_mul_assoc,smul_sub]
    abel
  change ‖U-V‖≤_
  rw [hsplit]
  have hi := hamiltonian_intertwiner_bound K L B (herm Z hZ) (herm D hD) T
  change ‖U*B-B*V‖≤_ at hi
  rw [hdef,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg h)] at hi
  calc
    _ ≤ ‖U*B-B*V‖+‖h • (U*X-X*V)‖ := norm_add_le _ _
    _ ≤ |T| * (h^2*‖X*D-Z*X‖)+|h| * (2*‖X‖) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add hi (mul_le_mul_of_nonneg_left hnorm (abs_nonneg _))
    _ = _ := by ring

/-- At a fixed displacement u in phase, a field increment u/T produces
an endpoint error bounded by a fixed numerator divided by T. -/
theorem inverse_time_field_bound (H Z D X : A) (hH : IsSelfAdjoint H)
    (hZ : IsSelfAdjoint Z) (hD : IsSelfAdjoint D) (hx : H*X-X*H=Z-D) (u T : ℝ) (hT : 0<T) :
    ‖evolve (H+(u/T) • Z) T-evolve (H+(u/T) • D) T‖≤
      (2*|u| * ‖X‖+u^2*‖X*D-Z*X‖)/T := by
  apply (field_evolution_bound H Z D X hH hZ hD hx (u/T) T).trans_eq
  rw [abs_div,abs_of_pos hT]
  field_simp

#print axioms inverse_time_field_bound
end
end GaloisForLFunctions.HTGeometry.Dephasing

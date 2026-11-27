import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw

/-! # A spin interchange tests the full deviation on the controlled branch -/
namespace GaloisForLFunctions.HTGeometry.TimePacking.IsolatedControls
noncomputable section
variable {A : Type*} [CStarAlgebra A]

/-- A unitary interchanging the two branches detects the entire deviation
of a controlled operator from the identity on its active branch. -/
theorem branch_deviation {P V W : A} (hP : ‖P‖ ≤ 1) (hV : V ∈ unitary A)
    (hflip : V*P=(1-P)*V) (hfix : W*(1-P)=1-P) :
    ‖W-1‖ ≤ ‖V*W-W*V‖ := by
  let R := W-1
  have hzero : R*(1-P)=0 := by simp only [R,sub_mul,one_mul,hfix,sub_self]
  have hkeep : R*P=R := by
    rw [mul_sub,mul_one,sub_eq_zero] at hzero
    exact hzero.symm
  have hblock : (V*W-W*V)*P=V*R := by
    rw [show V*W-W*V=V*R-R*V by simp only [R,mul_sub,sub_mul,mul_one,one_mul]; abel,
      sub_mul,mul_assoc,mul_assoc,hkeep,hflip,←mul_assoc,hzero,zero_mul,sub_zero]
  calc
    ‖W-1‖ = ‖V*R‖ := (CStarRing.norm_mem_unitary_mul _ hV).symm
    _ = ‖(V*W-W*V)*P‖ := congrArg norm hblock.symm
    _ ≤ ‖V*W-W*V‖*‖P‖ := norm_mul_le _ _
    _ ≤ ‖V*W-W*V‖ := mul_le_of_le_one_right (norm_nonneg _) hP

private theorem product_error {V T W U : A} (hT : ‖T‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    ‖V*W-T*U‖ ≤ ‖V-T‖+‖W-U‖ := by
  rw [show V*W-T*U=(V-T)*W+T*(W-U) by rw [sub_mul,mul_sub]; abel]
  apply (norm_add_le _ _).trans
  exact add_le_add ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hW))
    ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hT))

/-- If a physical pulse is within δ of an interchange, every operator
commuting with it stays at least half the controlled deviation minus δ
away. This applies at all dates of the same Hamiltonian. -/
theorem controlled_distance {P V W T U : A} (hP : ‖P‖ ≤ 1) (hV : V ∈ unitary A)
    (hflip : V*P=(1-P)*V) (hfix : W*(1-P)=1-P)
    (hW : ‖W‖ ≤ 1) (hT : ‖T‖ ≤ 1) (hc : Commute T U) :
    ‖W-1‖/2 ≤ ‖W-U‖+‖V-T‖ := by
  have hl := product_error (V:=V) (U:=U) hT hW
  have hr : ‖U*T-W*V‖ ≤ ‖W-U‖+‖V-T‖ := by
    rw [show U*T-W*V=(U-W)*T+W*(T-V) by rw [sub_mul,mul_sub]; abel]
    apply (norm_add_le _ _).trans
    rw [norm_sub_rev W U,norm_sub_rev V T]
    exact add_le_add ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hT))
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hW))
  rw [←hc.eq] at hr
  have h := (branch_deviation hP hV hflip hfix).trans
    ((norm_sub_le_norm_sub_add_norm_sub (V*W) (T*U) (W*V)).trans (add_le_add hl hr))
  linarith only [h]

/-- An approximate pulse tests every unitary commuting with the physical pulse. -/
theorem pulse_commutator {V T U : A} (hU : U∈unitary A) (hc : Commute T U) :
    ‖V*U-U*V‖ ≤ 2*‖V-T‖ := by
  rw [show V*U-U*V=(V-T)*U-U*(V-T) by rw [sub_mul,mul_sub,hc.eq]; abel]
  have h := norm_sub_le ((V-T)*U) (U*(V-T))
  rwa [CStarRing.norm_mul_mem_unitary _ hU,CStarRing.norm_mem_unitary_mul _ hU,←two_mul] at h

#print axioms controlled_distance
end
end GaloisForLFunctions.HTGeometry.TimePacking.IsolatedControls

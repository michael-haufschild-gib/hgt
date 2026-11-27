import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TimePacking.IsolatedControls.BranchComparison

/-! # Sharp projective exclusion from opposite branches of a reflection -/
namespace GaloisForLFunctions.HTGeometry.TimePacking.IsolatedControls
noncomputable section
variable {A : Type*} [CStarAlgebra A]

private theorem opposite_norms {U N : A} (hU : U∈unitary A) (hN : ‖N‖=1) :
    4 ≤ ‖U*N+N‖^2+‖U*N-N‖^2 := by
  let Y := U*N
  have hu : star Y*Y=star N*N := by
    rw [show Y=U*N from rfl,star_mul,mul_assoc,←mul_assoc (star U),
      (Unitary.mem_iff.mp hU).1,one_mul]
  have hg : star (Y+N)*(Y+N)+star (Y-N)*(Y-N)=(2:ℝ) • ((2:ℝ) • (star N*N)) := by
    rw [star_add,star_sub,two_smul,two_smul,add_mul,sub_mul,mul_add,mul_add,mul_sub,mul_sub,hu]
    abel
  have h := norm_add_le (star (Y+N)*(Y+N)) (star (Y-N)*(Y-N))
  rw [hg,norm_smul,norm_smul,CStarRing.norm_star_mul_self,CStarRing.norm_star_mul_self,
    CStarRing.norm_star_mul_self,hN] at h
  simpa only [Real.norm_ofNat,one_mul,mul_one,←sq,show (2:ℝ)*2=4 by norm_num] using h

/-- On a nonzero sector N, the target has opposite signs before and
after an ideal pulse V. A commuting physical unitary must pay the two
chordal distances to antipodes on that sector. -/
theorem antipodal_cost {U V W T N : A} (hU : U∈unitary A) (hV : V∈unitary A)
    (hN : ‖N‖=1) (hneg : W*N= -N) (hpos : W*(V*N)=V*N) (hc : Commute T U) :
    4 ≤ ‖U-W‖^2+(‖U-W‖+2*‖V-T‖)^2 := by
  have hsmall : ‖U*N+N‖ ≤ ‖U-W‖ := by
    rw [show U*N+N=(U-W)*N by rw [sub_mul,hneg,sub_neg_eq_add]]
    simpa only [hN,mul_one] using norm_mul_le (U-W) N
  have hcomm : ‖V*U-U*V‖ ≤ 2*‖V-T‖ := by
    rw [show V*U-U*V=(V-T)*U-U*(V-T) by rw [sub_mul,mul_sub,hc.eq]; abel]
    have h := norm_sub_le ((V-T)*U) (U*(V-T))
    rwa [CStarRing.norm_mul_mem_unitary _ hU,CStarRing.norm_mem_unitary_mul _ hU,←two_mul] at h
  have hsplit : V*(U*N-N)=(U-W)*(V*N)+(V*U-U*V)*N := by
    rw [mul_sub,sub_mul,sub_mul,mul_assoc U V N,mul_assoc V U N,hpos]
    abel
  have hother : ‖U*N-N‖ ≤ ‖U-W‖+2*‖V-T‖ := by
    rw [←CStarRing.norm_mem_unitary_mul (U*N-N) hV,hsplit]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simpa only [CStarRing.norm_mem_unitary_mul _ hV,hN,mul_one] using norm_mul_le (U-W) (V*N)
    · exact (norm_mul_le _ _).trans (by rw [hN,mul_one]; exact hcomm)
  exact (opposite_norms hU hN).trans (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hsmall 2)
    (pow_le_pow_left₀ (norm_nonneg _) hother 2))

#print axioms antipodal_cost
end
end GaloisForLFunctions.HTGeometry.TimePacking.IsolatedControls

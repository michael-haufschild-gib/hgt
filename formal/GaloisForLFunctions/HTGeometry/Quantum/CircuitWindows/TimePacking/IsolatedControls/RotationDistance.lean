import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TimePacking.IsolatedControls.BranchComparison

/-! # Distance to a rotation reversed by an approximately conserved pulse -/
namespace GaloisForLFunctions.HTGeometry.TimePacking.IsolatedControls
noncomputable section
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- For a rotation with real part c times identity, the sum of the two
squared distances to the forward and inverse rotations has a scalar floor. -/
private theorem paired_gram {U W : A} (hU : U∈unitary A) (hW : W∈unitary A)
    {c : ℝ} (hreal : W+star W=(2*c) • (1:A)) :
    4-4*|c| ≤ ‖U-W‖^2+‖U-star W‖^2 := by
  let B := star (U-W)*(U-W)+star (U-star W)*(U-star W)
  have hid : B+(2*c) • (star U+U)=(4:ℝ) • (1:A) := by
    have hleft := congrArg (fun X : A => star U*X) hreal
    have hright := congrArg (fun X : A => X*U) hreal
    change star U*(W+star W)=star U*((2*c) • (1:A)) at hleft
    change (W+star W)*U=((2*c) • (1:A))*U at hright
    rw [mul_add,mul_smul_comm,mul_one] at hleft
    rw [add_mul,smul_mul_assoc,one_mul] at hright
    dsimp only [B]
    simp only [star_sub,star_star,sub_mul,mul_sub,(Unitary.mem_iff.mp hU).1,
      (Unitary.mem_iff.mp hW).1,(Unitary.mem_iff.mp hW).2,smul_add,←hleft,←hright,
      show (4:ℝ)=(1+1)+(1+1) by norm_num,add_smul,one_smul]
    abel
  have hB := norm_add_le (star (U-W)*(U-W)) (star (U-star W)*(U-star W))
  simp only [CStarRing.norm_star_mul_self,←sq] at hB
  have hu := norm_add_le (star U) U
  rw [norm_star,CStarRing.norm_of_mem_unitary hU] at hu
  have hm := mul_le_mul_of_nonneg_left hu (abs_nonneg (2*c))
  have h := norm_add_le B ((2*c) • (star U+U))
  rw [hid,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,norm_one,mul_one] at h
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at h hm
  change ‖B‖ ≤ _ at hB
  rw [abs_of_nonneg (by norm_num : (0:ℝ)≤4)] at h
  linarith only [h,hm,hB]

/-- Conjugate rotations share a near fit whenever the physical evolution
commutes with a pulse within δ of the ideal conjugation. -/
theorem rotation_distance {U W V T : A} (hU : U∈unitary A) (hW : W∈unitary A)
    (hV : V∈unitary A) (hc : Commute T U) (hflip : V*W=star W*V)
    {c : ℝ} (hreal : W+star W=(2*c) • (1:A)) :
    Real.sqrt (2-2*|c|) ≤ ‖U-W‖+2*‖V-T‖ := by
  have hs : ‖U-star W‖ ≤ ‖U-W‖+2*‖V-T‖ := by
    rw [←CStarRing.norm_mul_mem_unitary (U-star W) hV,
      show (U-star W)*V=V*(U-W)-(V*U-U*V) by rw [sub_mul,mul_sub,hflip]; abel]
    exact (norm_sub_le _ _).trans (add_le_add (CStarRing.norm_mem_unitary_mul _ hV).le
      (pulse_commutator hU hc))
  have hr := (paired_gram hU hW hreal).trans
    (add_le_add_left (pow_le_pow_left₀ (norm_nonneg _) hs 2) _)
  have hx : ‖U-W‖ ≤ ‖U-W‖+2*‖V-T‖ := le_add_of_nonneg_right (by positivity)
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity,by linarith only [hr,pow_le_pow_left₀ (norm_nonneg _) hx 2]⟩

private theorem distance_one {W : A} (hW : W∈unitary A) {c : ℝ}
    (hreal : W+star W=(2*c) • (1:A)) (hc : c≤1) :
    ‖1-W‖=Real.sqrt (2-2*c) := by
  have hg : star (1-W)*(1-W)=(2-2*c) • (1:A) := by
    simp only [star_sub,star_one,sub_mul,mul_sub,one_mul,mul_one,(Unitary.mem_iff.mp hW).1,
      sub_smul,←hreal,two_smul]
    abel
  have h := congrArg norm hg
  rw [CStarRing.norm_star_mul_self,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith only [hc]),
    norm_one,mul_one,←sq] at h
  exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt h)

/-- One of the scalar phases ±1 realizes the midpoint distance of a rotation. -/
theorem scalar_midpoint {W : A} (hW : W∈unitary A) {c : ℝ} (hc : |c|≤1)
    (hreal : W+star W=(2*c) • (1:A)) :
    ∃ z : ℂ, ‖z‖=1 ∧ ‖z • (1:A)-W‖=Real.sqrt (2-2*|c|) := by
  by_cases h : 0≤c
  · refine ⟨1,norm_one,?_⟩
    rw [one_smul,abs_of_nonneg h]
    exact distance_one hW hreal ((le_abs_self _).trans hc)
  · have hn : -W∈unitary A := by
      apply Unitary.mem_iff.mpr
      simpa only [star_neg,neg_mul_neg] using Unitary.mem_iff.mp hW
    have he : -W+star (-W)=(2*(-c)) • (1:A) := by
      rw [star_neg,←neg_add,hreal,mul_neg,neg_smul]
    refine ⟨-1,by simp,?_⟩
    rw [neg_one_smul,abs_of_neg (lt_of_not_ge h),
      show -(1:A)-W= -(1- -W) by abel,norm_neg]
    exact distance_one hn he ((neg_le_abs _).trans hc)

#print axioms rotation_distance
end
end GaloisForLFunctions.HTGeometry.TimePacking.IsolatedControls

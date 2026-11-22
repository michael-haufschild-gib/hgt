import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.UnitaryChord
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw

/-! # Composition of physical circuit fits at twice the angle -/
open Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AngularError
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

private theorem phase_unitary {I : Type*} [Fintype I] [DecidableEq I] {U : Matrix I I ℂ}
    (hU : U ∈ unitary (Matrix I I ℂ)) {z : ℂ} (hz : ‖z‖=1) :
    z • U ∈ unitary (Matrix I I ℂ) := by
  have hc : star z*z=1 := by rw [Complex.star_def,Complex.conj_mul',hz]; norm_num
  have hc' : z*star z=1 := (mul_comm ..).trans hc
  obtain ⟨hl,hr⟩ := Unitary.mem_iff.mp hU
  apply Unitary.mem_iff.mpr
  simp only [star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hc,hc',hl,hr,one_smul,and_self]

/-- At equal input errors, multiplying the two fitted unitaries doubles
their angular tolerances. The two circuits and both phases may differ. -/
theorem affordable_add_angle {N i j : ℕ} (H : selfAdjoint (Reg N)) {x y θ : ℝ}
    (ht : 0≤θ) (hθ : 2*θ≤π/2)
    (hx : HasProjectiveCircuitApproximation N (2*sin θ) i (unitaryEvolution H.val x))
    (hy : HasProjectiveCircuitApproximation N (2*sin θ) j (unitaryEvolution H.val y)) :
    HasProjectiveCircuitApproximation N (2*sin (2*θ)) (i+j) (unitaryEvolution H.val (x+y)) := by
  obtain ⟨c,hc,C,hC,hx'⟩ := hx
  obtain ⟨d,hd,D,hD,hy'⟩ := hy
  let U := unitaryEvolution H.val x
  let V := unitaryEvolution H.val y
  let A : Reg N := c • (C.eval : Reg N)
  let B : Reg N := d • (D.eval : Reg N)
  have hU := unitaryEvolution_mem_unitary H.2 x
  have hV := unitaryEvolution_mem_unitary H.2 y
  have hA : A ∈ unitary (Reg N) := phase_unitary C.eval.property hc
  have hB : B ∈ unitary (Reg N) := phase_unitary D.eval.property hd
  have hVn : ‖V‖=1 := CStarRing.norm_coe_unitary (⟨V,hV⟩ : unitary (Reg N))
  have hAn : ‖A‖=1 := CStarRing.norm_coe_unitary (⟨A,hA⟩ : unitary (Reg N))
  have h₁ : ‖U*V-A*V‖ ≤ 2*sin θ := by
    rw [←sub_mul]
    exact (Matrix.l2_opNorm_mul _ _).trans (by rw [hVn,mul_one]; exact hx')
  have h₂ : ‖A*B-A*V‖ ≤ 2*sin θ := by
    rw [←mul_sub]
    exact (Matrix.l2_opNorm_mul _ _).trans (by rw [hAn,one_mul,norm_sub_rev B V]; exact hy')
  have hh := common_unitary_chord ((unitary _).mul_mem hU hV) ((unitary _).mul_mem hA hV)
    ((unitary _).mul_mem hA hB) ht hθ h₁ h₂
  have hprod : U*V=unitaryEvolution H.val (x+y) := by
    simpa only [add_sub_cancel_right] using unitaryEvolution_sub_mul H (x+y) y
  have hword : A*B=(c*d) • ((C.mul D).eval : Reg N) := by
    rw [TwoQubitCircuit.mul_eval]
    change (c • (C.eval : Reg N))*(d • (D.eval : Reg N)) = _
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rfl
  refine ⟨c*d,by rw [norm_mul,hc,hd,mul_one],C.mul D,?_,?_⟩
  · rw [TwoQubitCircuit.mul_gateCount]
    omega
  · rwa [hprod,hword] at hh

end
end GaloisForLFunctions.HTGeometry.AngularError

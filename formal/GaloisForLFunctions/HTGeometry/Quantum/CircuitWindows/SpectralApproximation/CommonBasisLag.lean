import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.BasisCost
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # Comparing two physical dates in the same arbitrary basis -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- A change of basis on both dates conjugates the generator of their
lag. Differencing the two circuits adds budgets and errors. -/
theorem common_basis_lag {N j s : ℕ} (H : selfAdjoint (Reg N))
    (W : unitaryGroup (Fin N → Bool) ℂ) {v w ε δ : ℝ}
    (hv : HasProjectiveCircuitApproximation N ε j (W.val*unitaryEvolution H.val v*star W.val))
    (hw : HasProjectiveCircuitApproximation N δ s (W.val*unitaryEvolution H.val w*star W.val)) :
    HasProjectiveCircuitApproximation N (ε+δ) (j+s) (W.val*unitaryEvolution H.val (w-v)*star W.val) := by
  let G : selfAdjoint (Reg N) := ⟨W.val*H.val*star W.val,by
    change star (W.val*H.val*star W.val)=W.val*H.val*star W.val
    simp only [star_mul,star_star,H.2.star_eq,mul_assoc]⟩
  have hunit : IsUnit W.val := ⟨⟨_,star W.val,W.property.2,W.property.1⟩,rfl⟩
  have hcov (t : ℝ) : unitaryEvolution G.val t=W.val*unitaryEvolution H.val t*star W.val := by
    simpa only [G,inv_eq_star_of_mem_unitary W.property] using unitaryEvolution_conj W.val H.val hunit t
  rw [←hcov] at hv hw ⊢
  exact (show -v+w=w-v by ring) ▸ affordable_add_time G (hv.neg_time G) hw

/-- Scalar affordability survives every change of basis at the same
operator tolerance, including at the boundary of a visit. -/
theorem conjugate_empty {N : ℕ} (W : unitaryGroup (Fin N → Bool) ℂ) {ε : ℝ} {U : Reg N}
    (h : HasProjectiveCircuitApproximation N ε 0 U) :
    HasProjectiveCircuitApproximation N ε 0 (W.val*U*star W.val) := by
  obtain ⟨z,hz,C,hC,he⟩ := h
  rw [zeroGateCircuit_eval C hC] at he
  refine ⟨z,hz,TwoQubitCircuit.one _,le_rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖W.val*U*star W.val-z • (1:Reg N)‖ ≤ ε
  rw [show W.val*U*star W.val-z • (1:Reg N)=W.val*(U-z • 1)*star W.val by
    simp only [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one,W.property.2],
    l2_opNorm_unitary_conj_eq W.property]
  exact he

/-- A circuit fitting in W coordinates can be run in V coordinates
by implementing the relative change of basis and its inverse. -/
theorem transfer_basis {N b j : ℕ} {δ ε : ℝ} (U V W : unitaryGroup (Fin N → Bool) ℂ)
    (hd : HasProjectiveCircuitApproximation N δ b (W*V⁻¹).val)
    (hc : HasProjectiveCircuitApproximation N ε j (W.val*U.val*star W.val)) :
    HasProjectiveCircuitApproximation N (ε+2*δ) (2*b+j) (V.val*U.val*star V.val) := by
  let D := W*V⁻¹
  let M := V*U*V⁻¹
  have he : D*M*D⁻¹=W*U*W⁻¹ := by simp [D,M,mul_assoc]
  have hm : HasProjectiveCircuitApproximation N ε j (D.val*M.val*star D.val) := by
    change HasProjectiveCircuitApproximation N ε j (D*M*D⁻¹).val
    rwa [he]
  exact cost_in_physical_basis M D hd hm

#print axioms transfer_basis
#print axioms common_basis_lag
#print axioms conjugate_empty
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation

import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.LocalGauge.BlockRotation

/-! # Exact scalar return dates on a coupled tangent perturbation -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.LocalGauge
noncomputable section
open PrecisionReturns

/-- Conjugation preserves empty-circuit distance for every matrix, since
one scalar phase suffices on either side of the comparison. -/
theorem scalar_distance_conjugate {n : ℕ} (U : Register n)
    (V : Matrix.unitaryGroup (Fin n→Bool) ℂ) :
    circuitDistance 0 (V.val*U*star V.val)=circuitDistance 0 U := by
  have hv := Unitary.mem_iff.mp V.2
  have hnorm (z : ℂ) : ‖V.val*U*star V.val-z • (1 : Register n)‖=‖U-z • 1‖ := by
    have he : V.val*(z • (1 : Register n))*star V.val=z • 1 := by
      rw [Matrix.mul_smul,mul_one,Matrix.smul_mul,hv.2]
    conv_lhs => rw [←he]
    rw [←Matrix.sub_mul,←Matrix.mul_sub,l2_opNorm_unitary_conj_eq V.2]
  have hfit (ε : ℝ) : HasProjectiveCircuitApproximation n ε 0 (V.val*U*star V.val) ↔
      HasProjectiveCircuitApproximation n ε 0 U := by
    constructor <;> rintro ⟨z,hz,C,hC,he⟩ <;> refine ⟨z,hz,C,hC,?_⟩ <;>
      rw [zeroGateCircuit_eval C hC] at he ⊢
    · rwa [hnorm] at he
    · rwa [hnorm]
  simp only [hasProjectiveCircuitApproximation_iff_infDist] at hfit
  exact le_antisymm ((hfit _).mpr le_rfl) ((hfit _).mp le_rfl)

/-- Along the straight tangent to a one-site phase rotation, the
entire empty-circuit distance profile depends on h only through the
nonnegative field increment √(1+h²)−1. -/
theorem tangent_scalar_profile {n : ℕ} (b : (Fin n→Bool)→Bool) (H : Register n) (h t : ℝ) :
    circuitDistance 0 (unitaryEvolution (H+h • tangent b H) t)=
      circuitDistance 0 (unitaryEvolution (H+(Real.sqrt (1+h^2)-1) • exchange b H) t) := by
  obtain ⟨V,he⟩ := tangent_conjugation b H h
  have hi : IsUnit V.val := ⟨⟨V.val,star V.val,(Unitary.mem_iff.mp V.2).2,(Unitary.mem_iff.mp V.2).1⟩,rfl⟩
  rw [he,←inv_eq_star_of_mem_unitary V.2,unitaryEvolution_conj _ _ hi,inv_eq_star_of_mem_unitary V.2]
  exact scalar_distance_conjugate _ V

#print axioms tangent_scalar_profile
end
end GaloisForLFunctions.HTGeometry.Dephasing.LocalGauge

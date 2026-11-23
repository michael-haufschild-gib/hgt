import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Charging the circuit implementing a change of basis -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation
noncomputable section

/-- Implementing a circuit in a changed basis costs two copies of that
basis change. Errors add in projective operator norm. -/
theorem cost_in_physical_basis {N b j : ℕ} {δ ε : ℝ}
    (U W : unitaryGroup (Fin N → Bool) ℂ)
    (hW : HasProjectiveCircuitApproximation N δ b W.val)
    (hU : HasProjectiveCircuitApproximation N ε j (W.val*U.val*star W.val)) :
    HasProjectiveCircuitApproximation N (ε+2*δ) (2*b+j) U.val := by
  have hadj : HasProjectiveCircuitApproximation N δ b (star W.val) := by
    obtain ⟨z,hz,C,hC,he⟩ := hW
    refine ⟨star z,(norm_star z).trans hz,C.adjoint,hC,?_⟩
    rw [TwoQubitCircuit.adjoint_eval]
    change ‖star W.val-star z • star C.eval.val‖ ≤ δ
    rwa [←star_smul,←star_sub,norm_star]
  let V := W*U*W⁻¹
  have hV : W.val*U.val*star W.val ∈ unitary _ := V.property
  have hw := LocalPatches.approx_product W.property (LocalPatches.approx_product hV hadj hU) hW
  have he : star W.val*(W.val*U.val*star W.val)*W.val=U.val := by
    calc _ = (star W.val*W.val)*U.val*(star W.val*W.val) := by simp only [mul_assoc]
         _ = _ := by rw [W.property.1,one_mul,mul_one]
  rwa [he,show δ+ε+δ=ε+2*δ by ring,show b+j+b=2*b+j by omega] at hw

#print axioms cost_in_physical_basis
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation

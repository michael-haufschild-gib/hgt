import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.RepeatedSteps
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.PathFactors

/-! # Arbitrary-order circuits for the time-independent Pauli chain -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
local instance repeatedPauliPathCStarAlgebra (n : ℕ) : CStarAlgebra (Reg n) where

/-- A circuit on the original qubits achieves error 1/100 at order j+1,
using exactly one gate for each rescaled Pauli exponential. -/
theorem exists_high_order_path_circuit {n : ℕ} (u : PathShell n) (j q : ℕ) (t : ℝ)
    (hq : 0 < q) (ht : 7^j*(1+∑ l : PathLabel n, |u l|)*|t| ≤ (q:ℝ)^(j+1)/100) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (n+2),
      C.gateCount = q^(j+2)*(3^j*Fintype.card (PathLabel n)) ∧
      ‖unitaryEvolution (pathHamiltonian u) t - c • (C.eval : Reg (n+2))‖ ≤ 1/100 := by
  obtain ⟨Z,hlen,hsum,hmass,hz,hs⟩ := exists_path_gate_generators u
  obtain ⟨w,hu,hw,he⟩ := ProductFormula.exists_repeated_word Z hz j
  have htime : 7^j*(1+ProductFormula.mass Z)*|t| ≤ (q:ℝ)^(j+1)/100 := by
    simpa only [ProductFormula.mass,hmass] using ht
  let h := t/((q:ℝ)^(j+2))
  have hf (y) (hy : y ∈ w) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (n+2),
      C.gateCount = 1 ∧ exp (h • y) = c • (C.eval : Reg (n+2)) := by
    obtain ⟨x,hx,b,rfl⟩ := hu y hy
    rw [Complex.coe_smul,smul_smul]
    exact hs (h*b) x hx
  obtain ⟨c,hc,C,hC,hprod⟩ := compile_path_word_steps w h hf
  let r := q^(j+2)
  refine ⟨c^r,by simp [norm_pow,hc],C.pow r,?_,?_⟩
  · rw [TwoQubitCircuit.pow_gateCount,hC,hw,hlen]
  have herr := he q t hq htime
  change ‖(w.map fun x => exp (h • x)).prod^r - exp (t • Z.sum)‖ ≤ _ at herr
  rw [hprod,smul_pow,hsum] at herr
  rw [TwoQubitCircuit.pow_eval_coe,norm_sub_rev]
  exact herr

#print axioms exists_high_order_path_circuit
end
end GaloisForLFunctions.HTGeometry

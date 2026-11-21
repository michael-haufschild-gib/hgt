import GaloisForLFunctions.HTGeometry.Quantum.CoefficientMassLieProduct
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.PathFactors

/-! # A sparse product formula for physical nearest-neighbour circuits -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
local instance (n : ℕ) : CStarAlgebra (Reg n) where

/-- Each Lie step uses exactly one gate per onsite or edge coefficient.
The error depends on the square of the integrated sum of coefficient
magnitudes, uniformly in chain length. -/
theorem exists_sparse_path_circuit {n : ℕ} (u : PathShell n) (t : ℝ) (r : ℕ) (hr : 0 < r) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (n+2),
      C.gateCount = r * Fintype.card (PathLabel n) ∧
      ‖unitaryEvolution (pathHamiltonian u) t - c • (C.eval : Reg (n+2))‖ ≤
        (∑ l : PathLabel n, |u l|)^2 * |t|^2/r := by
  obtain ⟨Z,hlen,hsum,hmass,hz,hs⟩ := exists_path_gate_generators u
  let h := t/(r:ℝ)
  obtain ⟨c,hc,C,hC,he⟩ := compile_path_word_steps Z h (hs h)
  refine ⟨c^r,by simp [norm_pow,hc],C.pow r,?_,?_⟩
  · simp only [TwoQubitCircuit.pow_gateCount,hC,hlen]
  have herr := list_lie_product_pow_mass_error Z hz t r hr
  change ‖(Z.map fun x => exp (h • x)).prod^r - exp (t • Z.sum)‖ ≤ _ at herr
  rw [he,smul_pow,hsum,hmass] at herr
  rw [TwoQubitCircuit.pow_eval_coe,norm_sub_rev]
  exact herr

#print axioms exists_sparse_path_circuit
end
end GaloisForLFunctions.HTGeometry

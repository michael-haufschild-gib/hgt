import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.CommutatorBounds.UnitaryPhases

/-! # Eigenbasis motion after matching two real spectra -/

open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.DiagonalCap.BalancedCuts
open DiagonalSynthesis.CommutatorBounds
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Once the energies are matched, an approximate intertwiner between
their diagonals almost commutes with the separated reference diagonal.
Rephasing the columns removes its remaining diagonal motion. -/
theorem transition_diagonal (Q : unitaryGroup I ℂ) (d f : I→ℝ) {g : ℝ} (hg : 0<g)
    (hsep : ∀ i j, i≠j → g≤|d i-d j|) :
    let Z := diagonal fun i => (d i:ℂ)
    let W := diagonal fun i => (f i:ℂ)
    ∃ φ : I→ℂ, (∀ i, ‖φ i‖=1) ∧
      ‖Q.val-diagonal φ‖ ≤ (2*sqrt packConstant/g)*(‖Z*Q.val-Q.val*W‖+‖W-Z‖) := by
  intro Z W
  obtain ⟨φ,hφ,_,herr⟩ := exists_diagonal_unitary Q.val Q.property
  refine ⟨φ,hφ,?_⟩
  have he : Z*Q.val-Q.val*Z=(Z*Q.val-Q.val*W)+Q.val*(W-Z) := by rw [mul_sub]; abel
  have hcomm : ‖Z*Q.val-Q.val*Z‖≤‖Z*Q.val-Q.val*W‖+‖W-Z‖ := by
    rw [he]
    exact (norm_add_le ..).trans_eq (by rw [CStarRing.norm_mem_unitary_mul Q.property])
  have hbound := (offDiagonal_le_commutator d hg hsep Q.val).trans
    (mul_le_mul_of_nonneg_left hcomm (div_nonneg (sqrt_nonneg _) hg.le))
  exact (herr.trans (mul_le_mul_of_nonneg_left hbound zero_le_two)).trans_eq (by ring)

#print axioms transition_diagonal
end
end GaloisForLFunctions.HTGeometry.WeakBonds.DiagonalCap.BalancedCuts

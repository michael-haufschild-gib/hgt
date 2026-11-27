import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.ComponentCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.CalibratedSubset
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.Outliers.LocalRows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.RepeatedBudget

/-! # The cost of merging components with local exceptions -/
open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit FixedHorizon RepeatedGates RepeatedGates.PhysicalBlocks RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
noncomputable section
variable {n : ℕ}

/-- All calls beyond component mergers are added to the spanning cost.
Only weak edges, local cap failures, boundary strips and unresolved
packets are subtracted. -/
theorem merge_budget_with_outliers (ω : PathPauliDisorder) (C : TwoQubitCircuit (n+2))
    {t h B γ : ℝ} (ht : 0<t) (hh : 0<h) (hB : 0≤B) (hsmall : 3348*t*B≤1)
    (R k : ℕ) (hk : 16<(k:ℝ)*(t*h)) (hweak : 36* |t| *γ≤(t*h)/16)
    (z : ℂ) (hz : ‖z‖=1) (hf : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4) :
    let u := pathPauliDisorderShell ω n
    n+1+redundant (circuitWord C)≤C.gateCount+(weakEdges u h).card+(exceptionalEdges u B).card+
      2*(2*(2*R+2)*(k*k)+(missedBonds n R γ ω).card+2*R) := by
  classical
  intro u
  let W := weakEdges u h∪exceptionalEdges u B
  obtain ⟨cut,hparts⟩ := component_cut C
  have hc := crossed_edges_outside ω C cut W ht hh hB subset_union_left
    (fun a e he => rotated_cap_at_row a u (fun hb => he (mem_union_right _ hb))) hsmall R k hk hweak z hz hf
  have hW : W.card≤_ := Finset.card_union_le (weakEdges u h) (exceptionalEdges u B)
  have hm := repeat_budget (circuitWord C)
  rw [Fintype.card_fin,circuitWord_length] at hm
  omega

#print axioms merge_budget_with_outliers
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

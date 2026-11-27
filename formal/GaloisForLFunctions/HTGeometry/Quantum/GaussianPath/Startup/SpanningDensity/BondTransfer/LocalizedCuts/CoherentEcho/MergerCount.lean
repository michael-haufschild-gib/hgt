import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.Selection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.Matching.Longitudinal
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.Calibration.RotatedDraw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.ComponentCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.RepeatedBudget

/-! # Component mergers paid for by coherent cut echoes in two frames -/
open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open LocalEcho WeakBondDeficit RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback RepeatedGates.PhysicalBlocks
noncomputable section
variable {n : ℕ}

/-- Apart from weak physical bonds, at most 2k mergers can be lost
when k equally strong crossed bonds force a coherent half turn. -/
theorem echo_merge_budget (u : PathShell n) (C : TwoQubitCircuit (n+2))
    (k : ℕ) {t B h : ℝ} (ht : 0<t) (hB : 0≤B) (cap : ∀ l, |u l|≤B)
    (hphase : π≤4*t*((k:ℝ)*h)) (hs : t*(43*B)≤1/100)
    (hv : (k:ℝ)*(43*B)^2*t^2≤1/1000000) (z : ℂ) (hz : ‖z‖=1)
    (hf : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4) :
    n+1+redundant (circuitWord C)≤C.gateCount+(weakEdges u h).card+2*k := by
  obtain ⟨c,hparts⟩ := component_cut C
  have hc := crossed_from_longitudinal u C c _ (fun _ he => he) k z hf (by
    intro a D d G v he hG hg
    exact (echo_strong_count v D d G hG k ht (by positivity : 0≤43*B)
      (fun e _ => echo_local_mass v (rotated_coordinate_cap a u cap) e)
      (fun e hmem => (hg e hmem).2.le) hphase hs hv z hz he).le)
  have hr := repeat_budget (circuitWord C)
  rw [Fintype.card_fin,circuitWord_length] at hr
  omega

#print axioms echo_merge_budget
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

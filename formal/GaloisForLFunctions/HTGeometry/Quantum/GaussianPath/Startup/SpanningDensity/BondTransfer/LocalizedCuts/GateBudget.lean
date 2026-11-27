import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.DetectedFamily
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.CalibratedFamily
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.ComponentCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.RepeatedBudget

/-! # Physical gate count from finitely localized cut reporters -/
open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon WeakBondDeficit RepeatedGates RepeatedGates.PhysicalBlocks RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
noncomputable section
variable {n : ℕ}

/-- Localization avoids any density loss from weak boundary seams. At a
fixed radius the remaining packet allowance is of order (th)⁻². -/
theorem local_merge_budget (ω : PathPauliDisorder) (C : TwoQubitCircuit (n+2))
    (p k : ℕ) {t h B : ℝ} (ht : 0<t) (hh : 0<h) (hB : 0≤B)
    (cap : ∀ l, |pathPauliDisorderShell ω n l|≤B) (hsmall : 3348*t*B≤1)
    (hloc : 2*(2*(21*(2*(p:ℝ)+2))*B)^p*t^p≤t*h/16) (hk : 16<(k:ℝ)*(t*h))
    (z : ℂ) (hz : ‖z‖=1) (hf : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4) :
    n+1+redundant (circuitWord C)≤C.gateCount+(weakEdges (pathPauliDisorderShell ω n) h).card+
      2*(2*(2*p+4)*(k*k)) := by
  obtain ⟨c,hparts⟩ := component_cut C
  have hc := crossed_from_detectable ω C c _ ht hh hB (fun _ he => he)
    (fun a _ _ l _ => rotated_coordinate_cap a _ cap l) hsmall (2*(2*p+4)*(k*k)) z hf
    (fun a D d he => (local_detected_cut_count _ D d p k ht.le (mul_pos ht hh) hB
      (rotated_coordinate_cap a _ cap) hloc hk z hz he).le)
  have hm := repeat_budget (circuitWord C)
  rw [Fintype.card_fin,circuitWord_length] at hm
  omega

#print axioms local_merge_budget
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

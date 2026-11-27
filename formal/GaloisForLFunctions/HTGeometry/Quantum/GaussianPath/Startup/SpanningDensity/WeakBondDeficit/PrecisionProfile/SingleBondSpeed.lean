import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.QuadraticPrecision.SingleBond
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.ComponentCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.RepeatedBudget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Initial distance cost of an uncovered physical bond -/
open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BondTransfer RepeatedGates RepeatedGates.PhysicalBlocks RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
noncomputable section
variable {n : ℕ}

/-- If fewer than d bonds lie in the h-box, any circuit missing d calls
from a sweep leaves a strong bond across a component cut. For sufficiently
short positive times this alone costs more than th/2 in operator error. -/
theorem rank_single_signal_lower (ω : PathPauliDisorder) (d : ℕ) {h t : ℝ} (hh : 0<h) (ht : 0<t)
    (hd : d≤n+1) (hw : (weakEdges (pathPauliDisorderShell ω n) h).card<d)
    (hsmall : 3348*t*‖pathPauliDisorderShell ω n‖≤1) :
    t*h/2<Metric.infDist (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)
      (phaseCircuitMatrixImageAtMost (n+2) (n+1-d)) := by
  classical
  let u := pathPauliDisorderShell ω n
  have hlabels : largeLabels u ‖u‖=∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr fun l hl => (mem_filter.mp hl).2.not_ge (abs_coord_le_norm u l)
  have hout := exceptionalEdges_card u ‖u‖
  rw [hlabels,Finset.card_empty,Nat.mul_zero] at hout
  by_contra! hfit
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hfit
  obtain ⟨c,hparts⟩ := component_cut C
  have hcut := fine_crossed_edges ω C c ht hh (norm_nonneg u) hsmall (ε:=t*h/2) (by linarith) z hz he
  have hword := repeat_budget (circuitWord C)
  rw [Fintype.card_fin,circuitWord_length] at hword
  change (crossed c).card≤(weakEdges u h).card+(exceptionalEdges u ‖u‖).card at hcut
  change (weakEdges u h).card<d at hw
  omega

#print axioms rank_single_signal_lower
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit

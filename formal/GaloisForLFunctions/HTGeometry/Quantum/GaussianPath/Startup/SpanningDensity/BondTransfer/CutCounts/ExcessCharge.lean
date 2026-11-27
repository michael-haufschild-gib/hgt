import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.PhysicalEdges
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.BoxCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.PhysicalGateCharge

/-! # Finite-size excess over a physical bond sweep -/

open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon WeakBondDeficit RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
open RepeatedGates.PhysicalBlocks RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section
variable {n : ℕ}

/-- Each calibrated triple charges nonmerging gate calls. The sole loss
in the spanning cost is bounded by weak central bonds, insufficient transfer
on separated packets, and missed boundary strips. -/
theorem physical_excess_charge (ω : PathPauliDisorder) (C : TwoQubitCircuit (n+2))
    {t h B γ δ : ℝ} (ht : 0<t) (hh : 0<h) (hB : 0≤B)
    (cap : ∀ l, |pathPauliDisorderShell ω n l|≤B) (hsmall : 3348*t*B≤1)
    (R k : ℕ) (hk : 16<(k:ℝ)*(t*h)) (hweak : 36* |t| *γ≤(t*h)/16)
    (hδ : 0≤δ) (hsin : 0<(sin t)^2) (herr : 252* |t| * δ≤(sin t)^2/4)
    (z : ℂ) (hz : ‖z‖=1) (hf : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4) :
    let loss := (weakEdges (pathPauliDisorderShell ω n) h).card+
      2*(2*(2*R+2)*(k*k)+(missedBonds n R γ ω).card+2*R)
    ((n+1:ℕ):ℝ)+((goodBoxes (1/sqrt 2) δ ω ((n+1)/4)).card:ℝ)*(sin t)^8/546≤
      (C.gateCount:ℝ)+(loss:ℝ)+1 := by
  intro loss
  obtain ⟨cut,hparts⟩ := component_cut C
  have hcut : (crossed cut).card≤loss :=
    crossed_physical_edges ω C cut ht hh hB cap hsmall R k hk hweak z hz hf
  have hp : (parts (circuitWord C)).card≤loss+1 := hparts.trans (Nat.add_le_add_right hcut _)
  have hm := repeat_budget (circuitWord C)
  rw [Fintype.card_fin,circuitWord_length] at hm
  have hc : n+1+redundant (circuitWord C)≤C.gateCount+loss := by omega
  have hc' := (Nat.cast_le (α:=ℝ)).mpr hc
  push_cast only [Nat.cast_add,Nat.cast_one] at hc' ⊢
  have hbox := boxes_force_repeated_calls ω C hδ hsin herr z hz hf
  linarith only [hc',hbox]

#print axioms physical_excess_charge
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

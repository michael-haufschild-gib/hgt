import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.CalibratedFamily
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.DetectedCuts

/-! # Counting crossed edges outside any declared exceptional set -/

open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- Every strong crossed edge outside W has its own maximizing Pauli
frame. It suffices to bound the coordinates within one row of that edge. -/
theorem crossed_edges_outside (ω : PathPauliDisorder) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (W : Finset (Fin (n+1))) {t h B γ : ℝ} (ht : 0<t) (hh : 0<h) (hB : 0≤B)
    (weakW : weakEdges (pathPauliDisorderShell ω n) h⊆W)
    (cap : ∀ (a : Fin (n+2)→Fin 3) (e : Fin (n+1)), e∉W → ∀ l : PathLabel n,
      (pathPauliSourceCoordinate l).1≤e.val+1 ∧ e.val≤(pathPauliSourceCoordinate l).1+1 →
      |rotatedShell a (pathPauliDisorderShell ω n) l|≤B)
    (hsmall : 3348*t*B≤1) (R k : ℕ) (hk : 16<(k:ℝ)*(t*h)) (hweak : 36* |t| *γ≤(t*h)/16)
    (z : ℂ) (hz : ‖z‖=1) (hf : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4) :
    (crossed c).card≤W.card+2*(2*(2*R+2)*(k*k)+(missedBonds n R γ ω).card+2*R) := by
  apply crossed_from_detectable ω C c W ht hh hB weakW cap hsmall _ z hf
  intro a D c' u' hfit
  let ω' := rotatedDraw a ω
  have he : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω' n)) t-z • D.eval.val‖≤1/4 := by
    rwa [shell_rotated_draw]
  have hcount := detected_cut_count ω' D c' (mul_pos ht hh) R k hk hweak z hz he
  rw [shell_rotated_draw,rotated_missed_bonds] at hcount
  exact hcount.le

#print axioms crossed_edges_outside
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

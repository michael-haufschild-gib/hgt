import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.CalibratedSubset

/-! # Counting every crossed physical edge from calibrated bond signals -/

open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- A fitting circuit has few crossed physical bonds, even if every bond
has a different strongest Pauli coupling and sign. Weak bonds and missed
bracketing strips enter separately, with no independence assumption. -/
theorem crossed_physical_edges (ω : PathPauliDisorder) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    {t h B γ : ℝ} (ht : 0<t) (hh : 0<h) (hB : 0≤B)
    (cap : ∀ l, |pathPauliDisorderShell ω n l|≤B) (hsmall : 3348*t*B≤1)
    (R k : ℕ) (hk : 16<(k:ℝ)*(t*h)) (hweak : 36* |t| *γ≤(t*h)/16)
    (z : ℂ) (hz : ‖z‖=1) (hf : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4) :
    (crossed c).card≤(weakEdges (pathPauliDisorderShell ω n) h).card+
      2*(2*(2*R+2)*(k*k)+(missedBonds n R γ ω).card+2*R) := by
  exact crossed_edges_outside ω C c _ ht hh hB (fun _ he => he)
    (fun a _ _ l _ => rotated_coordinate_cap a _ cap l) hsmall R k hk hweak z hz hf

#print axioms crossed_physical_edges
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

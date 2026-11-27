import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.Matching.Maximum

/-! # Counting crossed bonds in two product frames -/

open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit LocalEcho
noncomputable section
variable {n : ℕ}

/-- A longitudinal count in every product frame bounds the full set
of crossed strong physical bonds by twice that count. Within a matching
all maximizing choices of the two Pauli axes extend to one frame. -/
theorem crossed_from_longitudinal (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (W : Finset (Fin (n+1))) {t h ε : ℝ} (weakW : weakEdges u h⊆W) (M : ℕ) (z : ℂ)
    (fit : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤ε)
    (bound : ∀ (a : Fin (n+2)→Fin 3) (D : TwoQubitCircuit (n+2)) (d : Cut D) (G : Finset (Fin (n+1))),
      let v := rotatedShell a u
      ‖unitaryEvolution (pathHamiltonian v) t-z • D.eval.val‖≤ε → G⊆crossed d →
      (∀ e∈G, e∉W ∧ h < |v (zz e)|) → G.card≤M) : (crossed c).card≤W.card+2*M := by
  exact crossed_from_maximal_axes u C c W weakW M z fit (fun a D d G he hG hg =>
    bound a D d G he hG (fun e hh => ⟨(hg e hh).1,(hg e hh).2.1⟩))

#print axioms crossed_from_longitudinal
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

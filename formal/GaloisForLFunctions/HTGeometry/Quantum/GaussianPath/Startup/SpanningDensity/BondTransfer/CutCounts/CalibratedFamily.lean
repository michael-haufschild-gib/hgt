import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Disorder.Rows.Incidence
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.Calibration.RotatedDraw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.CrossedSignals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.Detection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.Matching.Maximum

/-! # From calibrated cut tests to counts of physical bonds -/

open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- Two product frames suffice to count the crossed bonds outside W. In
each parity class the maximizing Pauli axes can be chosen simultaneously.
Any uniform count for the resulting detectable edges transfers back. -/
theorem crossed_from_detectable (ω : PathPauliDisorder) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (W : Finset (Fin (n+1))) {t h B ε : ℝ} (ht : 0<t) (_hh : 0<h) (hB : 0≤B)
    (weakW : weakEdges (pathPauliDisorderShell ω n) h⊆W)
    (cap : ∀ (a : Fin (n+2)→Fin 3) (e : Fin (n+1)), e∉W → ∀ l : PathLabel n,
      (pathPauliSourceCoordinate l).1≤e.val+1 ∧ e.val≤(pathPauliSourceCoordinate l).1+1 →
      |rotatedShell a (pathPauliDisorderShell ω n) l|≤B)
    (hsmall : 3348*t*B≤1) (M : ℕ) (z : ℂ)
    (hf : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤ε)
    (bound : ∀ (a : Fin (n+2)→Fin 3) (D : TwoQubitCircuit (n+2)) (c' : Cut D),
      let u' := rotatedShell a (pathPauliDisorderShell ω n)
      ‖unitaryEvolution (pathHamiltonian u') t-z • D.eval.val‖≤ε →
      (detectable c' u' t (t*h)).card≤M) : (crossed c).card≤W.card+2*M := by
  let u := pathPauliDisorderShell ω n
  apply crossed_from_maximal_axes u C c W weakW M z hf
  intro a D d G v he hG hh
  have hsub : G⊆detectable d v t (t*h) := by
    intro e hmem
    obtain ⟨hout,hstrong,hmax⟩ := hh e hmem
    have hb := cap a e hout (bondLabel e) ⟨Nat.le_succ _,Nat.le_succ _⟩
    have hsignal := detectable_bond v e ht.le hB
      (fun l hl => cap a e hout l (source_row_at_edge hl)) hb hmax hsmall
    exact mem_filter.mpr ⟨hG hmem,(mul_lt_mul_of_pos_left hstrong ht).trans_le hsignal⟩
  exact (card_le_card hsub).trans (bound a D d he)

#print axioms crossed_from_detectable
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

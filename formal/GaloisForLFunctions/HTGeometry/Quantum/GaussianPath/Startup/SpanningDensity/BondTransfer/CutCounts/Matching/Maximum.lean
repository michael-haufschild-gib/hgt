import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.SparseMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.Calibration.RotatedDraw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.CircuitFit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.MatchedAxes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.BondSets

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
theorem crossed_from_maximal_axes (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (W : Finset (Fin (n+1))) {t h ε : ℝ} (weakW : weakEdges u h⊆W) (M : ℕ) (z : ℂ)
    (fit : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤ε)
    (bound : ∀ (a : Fin (n+2)→Fin 3) (D : TwoQubitCircuit (n+2)) (d : Cut D) (G : Finset (Fin (n+1))),
      let v := rotatedShell a u
      ‖unitaryEvolution (pathHamiltonian v) t-z • D.eval.val‖≤ε → G⊆crossed d →
      (∀ e∈G, e∉W ∧ h < |v (zz e)| ∧ ∀ ab : Fin 3×Fin 3, |v (.inr (e,ab))|≤|v (zz e)|) → G.card≤M) : (crossed c).card≤W.card+2*M := by
  classical
  let F := crossed c \ W
  have witness (e : Fin (n+1)) : ∃ b : Fin 3×Fin 3, ∀ q, |u (.inr (e,q))|≤|u (.inr (e,b))| := by
    obtain ⟨b,_,hb⟩ := univ.exists_max_image (fun q : Fin 3×Fin 3 => |u (.inr (e,q))|) univ_nonempty
    exact ⟨b,fun q => hb q (mem_univ _)⟩
  choose b hb using witness
  have for_parity (p : ℕ) : (F.filter (fun e => e.val%2=p)).card≤M := by
    let G := F.filter (fun e => e.val%2=p)
    have hmatch : ∀ e∈G, ∀ f∈G, e.castSucc≠f.succ := by
      intro e he f hf h
      have hval : e.val=f.val+1 := congrArg Fin.val h
      have h₁ := (mem_filter.mp he).2
      have h₂ := (mem_filter.mp hf).2
      omega
    obtain ⟨a,ha⟩ := axis_frame_on_matching G b hmatch
    obtain ⟨T,hT⟩ := frame_preserves_fit a u C t z
    let D : TwoQubitCircuit (n+2) := ⟨C.gateCount,C.architecture,T⟩
    let c' : Cut D := ⟨c.val,c.property⟩
    let u' := rotatedShell a u
    have hc : crossed c'=crossed c := by ext e; simp only [mem_crossed_iff,c']
    apply bound a D c' G (hT.trans_le fit) (fun e he => hc.symm ▸ (mem_sdiff.mp (mem_filter.mp he).1).1)
    intro e he
    have hF := mem_sdiff.mp (mem_filter.mp he).1
    have hmax : |u' (zz e)|=|u (.inr (e,b e))| := (rotatedShell_longitudinal a u e).trans (by rw [ha e he])
    refine ⟨hF.2,?_,?_⟩
    · change h < |u' (zz e)|
      rw [hmax]
      by_contra! hle
      exact hF.2 (weakW (mem_filter.mpr ⟨mem_univ _,fun q => (hb e q).trans hle⟩))
    · intro ab
      change |rotatedShell a u (.inr (e,ab))|≤|u' (zz e)|
      rw [hmax,rotated_bond_magnitude]
      exact hb e _
  have hcov : F⊆F.filter (fun e => e.val%2=0)∪F.filter (fun e => e.val%2=1) := by
    intro e he
    by_cases h : e.val%2=0
    · exact mem_union_left _ (mem_filter.mpr ⟨he,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨he,by omega⟩)
  have hc := ((card_le_card hcov).trans (card_union_le _ _)).trans (add_le_add (for_parity 0) (for_parity 1))
  have hN : (crossed c).card≤F.card+W.card := by
    rw [←card_sdiff_add_card_inter (crossed c) W]
    exact Nat.add_le_add_left (card_le_card inter_subset_right) _
  change (crossed c).card≤W.card+2*M
  omega

#print axioms crossed_from_maximal_axes
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

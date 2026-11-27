import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.JoinHamiltonian
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.PhysicalEnergies
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.SpectralStability

/-! # The tensor-sum gap survives insertion of one physical bond -/
open Set Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open FirstAscent.ThermodynamicEdges
noncomputable section

/-- Every pair of child levels is an actual level of the decoupled register. -/
theorem sum_mem_spectrum (l r : ℕ) (x : PathLabel (l+r+2)→ℝ)
    (i : Fin (2^(l+2))) (j : Fin (2^(r+2))) :
    ((energies l (extractBlocks l r x).1.1 i+energies r (extractBlocks l r x).1.2 j : ℝ):ℂ)
      ∈ spectrum ℂ (blockSum l r x) := by
  classical
  let m := l+r+2
  let S := intervalWires (m+2) 0 (l+2)
  let T := intervalWires (m+2) (l+2) (r+2)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i h₁ h₂
    have hL := (mem_filter.mp h₁).2.2
    have hR := (mem_filter.mp h₂).2.1
    omega
  let e := numberWires (B:=0) (m:=l) (n:=m) (by dsimp only [m]; omega)
  let f := numberWires (B:=l+2) (m:=r) (n:=m) (by dsimp only [m]; omega)
  let eL := Equiv.arrowCongr e (Equiv.refl Bool)
  let eR := Equiv.arrowCongr f (Equiv.refl Bool)
  let u : PathShell l := WithLp.toLp 2 (extractBlocks l r x).1.1
  let v : PathShell r := WithLp.toLp 2 (extractBlocks l r x).1.2
  let hL := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let hR := (isSelfAdjoint_pathHamiltonian v).isHermitian
  let hA := isHermitian_reindex eL hL
  let hB := isHermitian_reindex eR hR
  have hsum : (blockSum l r x).IsHermitian :=
    (isHermitian_liftLocalMatrix (A:=fun _ : Fin (m+2) => Bool) S hA).add
      (isHermitian_liftLocalMatrix (A:=fun _ : Fin (m+2) => Bool) T hB)
  have ha : energies l (extractBlocks l r x).1.1 i ∈ range hA.eigenvalues := by
    rw [range_eigenvalues_reindex eL hL,←energies_range]
    exact mem_range_self _
  have hb : energies r (extractBlocks l r x).1.2 j ∈ range hB.eigenvalues := by
    rw [range_eigenvalues_reindex eR hR,←energies_range]
    exact mem_range_self _
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  rw [hsum.spectrum_eq_image_range]
  refine ⟨_,?_,rfl⟩
  exact (range_eigenvalues_add_liftLocalMatrix_disjoint hd hA hB hsum).ge
    ⟨(a,b),congrArg₂ (·+·) ha hb⟩

/-- With a joining bond of size below one quarter of the product spacing,
the sorted physical energy array keeps at least half that spacing. -/
theorem physical_merge_gap (l r : ℕ) (x : PathLabel (l+r+2)→ℝ) {g : ℝ} (hg : 0<g)
    (hgap : ∀ a b : Fin (2^(l+2))×Fin (2^(r+2)), a≠b → g ≤
      |(energies l (extractBlocks l r x).1.1 a.1 + energies r (extractBlocks l r x).1.2 a.2)-
       (energies l (extractBlocks l r x).1.1 b.1 + energies r (extractBlocks l r x).1.2 b.2)|)
    (hseam : ∀ j, |(extractBlocks l r x).2 j| ≤ g/40) :
    ∀ i j, i≠j → g/2 ≤ |energies (l+r+2) x i-energies (l+r+2) x j| := by
  classical
  let m := l+r+2
  let v : PathShell m := WithLp.toLp 2 x
  let H := pathHamiltonian v
  let hH := (isSelfAdjoint_pathHamiltonian v).isHermitian
  let e : (Fin (m+2)→Bool) ≃ Fin (2^(l+2))×Fin (2^(r+2)) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Fintype.card_prod]
    rw [←pow_add]; congr 1; dsimp only [m]; omega)
  let d (p : Fin (2^(l+2))×Fin (2^(r+2))) := energies l (extractBlocks l r x).1.1 p.1+energies r (extractBlocks l r x).1.2 p.2
  have hd : ‖blockSum l r x-H‖<g/4 :=
    (seam_error l r x hseam).trans_lt (by linarith only [hg])
  have hh := stable_spacing _ H hH (fun i => d (e i))
    (fun i => sum_mem_spectrum l r x (e i).1 (e i).2) hg
    (fun i j h => hgap (e i) (e j) (e.injective.ne h)) hd
  exact transfer_spacing (qubitConfigFin (m+2)) (energies_range (n:=m) x).ge (half_pos hg) hh

#print axioms physical_merge_gap
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers

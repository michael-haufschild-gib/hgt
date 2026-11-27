import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.ProductEvent
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.SumSpectrum

/-! # Probability retained at one balanced physical merger -/
open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section

/-- Product levels separated at twice the parent scale survive a seam
whose nine Pauli coefficients each cost at most a twentieth of that scale. -/
theorem balanced_merge_mass (l r : ℕ) (hl : l≤r) (hr : r≤l+1) :
    gapMass l*gapMass r*(standardLaw (Fin 3×Fin 3)).real (seamBox (gapScale (l+r+4)/20)) ≤
      (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))*gapMass (l+r+2) := by
  apply joined_event_mass l r hl hr
  intro x hgap hseam i j hij
  have hg := gapScale_pos (l+r+4)
  have hs t : |(extractBlocks l r x).2 t|≤gapScale (l+r+4)/20 := abs_le.mpr (hseam t (mem_univ t))
  have h := physical_merge_gap l r x (mul_pos two_pos hg) hgap (fun t => (hs t).trans (by linarith only [hg])) i j hij
  simpa only [show 2*gapScale (l+r+4)/2=gapScale (l+r+4) by ring] using h

#print axioms balanced_merge_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers

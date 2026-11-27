import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.JoinLabels
import GaloisForLFunctions.HTGeometry.ObserverJacobianFullGaussianTubeLaw

/-! # Exact independent Gaussian split at a joining bond -/
open MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section

abbrev standardLaw (ι : Type*) [Fintype ι] := Measure.pi fun _ : ι => gaussianReal 0 1

/-- Left and right block coefficients are read in their original path order. -/
def extractBlocks (l r : ℕ) (x : PathLabel (l+r+2)→ℝ) :
    ((PathLabel l→ℝ)×(PathLabel r→ℝ))×(Fin 3×Fin 3→ℝ) :=
  ((fun i => x (joinLabel l r (.inl i)),fun i => x (joinLabel l r (.inr (.inl i)))),
    fun i => x (joinLabel l r (.inr (.inr i))))

theorem extractBlocks_law (l r : ℕ) :
    MeasurePreserving (extractBlocks l r) (standardLaw (PathLabel (l+r+2)))
      (((standardLaw (PathLabel l)).prod (standardLaw (PathLabel r))).prod (standardLaw (Fin 3×Fin 3))) := by
  let e := (Equiv.sumAssoc (PathLabel l) (PathLabel r) (Fin 3×Fin 3)).trans (joinEquiv l r)
  let G := fun _ : PathLabel (l+r+2) => gaussianReal 0 1
  have hi := (measurePreserving_piCongrLeft G e).symm (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e)
  have h₁ := measurePreserving_sumPiEquivProdPi (fun _ : (PathLabel l ⊕ PathLabel r) ⊕ (Fin 3×Fin 3) => gaussianReal 0 1)
  have h₂ := measurePreserving_sumPiEquivProdPi (fun _ : PathLabel l ⊕ PathLabel r => gaussianReal 0 1)
  exact (h₂.prod (MeasurePreserving.id (standardLaw (Fin 3×Fin 3)))).comp (h₁.comp hi)

#print axioms extractBlocks_law
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers

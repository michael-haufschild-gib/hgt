import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpProjectiveEuclideanAction

/-!
# One-sided inclusion tests for canonical completed Cartan coordinates

After an arbitrary matrix-image lattice is put in its canonical dominant Cartan frame, sharp
uniformizer-scaled inclusions are exactly coordinatewise lower or upper bounds on its relative
position vector.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K] {r : ℕ}

/-- Scaling a matrix-image lattice into the standard lattice is exactly a lower bound on every
canonical Cartan coordinate. -/
theorem leftScale_uniformizer_mapMatrix_standard_carrier_le_iff_relativePosition
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ) (z : ℤ) :
    (leftScaleCompletedPseudoDiffOpLattice
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ z)
      (mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpMatrixLinearEquiv A)
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)))).carrier ≤
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)).carrier ↔
      ∀ i, 0 ≤ completedPseudoDiffOpDominantRelativePosition
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))) i + z := by
  let L := standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)
  let M := mapCompletedPseudoDiffOpLatticeLinear
    (completedPseudoDiffOpMatrixLinearEquiv A) L
  let d := completedPseudoDiffOpDominantCartanData L M
  rw [← mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame]
  rw [mapCompletedPseudoDiffOpLatticeLinear_leftScale, d.map_right, d.map_left,
    leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const,
    ← standardCompletedPseudoDiffOpLatticeAtCoweight_zero,
    standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff]
  rw [standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
  simp only [Pi.add_apply]
  change (∀ i, 0 ≤ d.coweight i + z) ↔ ∀ i, 0 ≤
    completedPseudoDiffOpDominantRelativePosition L M i + z
  rw [show d.coweight = completedPseudoDiffOpDominantRelativePosition L M from
    completedPseudoDiffOpDominantRelativePosition_eq L M d.frame d.coweight
      d.map_left d.map_right d.dominant]

/-- Containing the standard lattice after scaling is exactly an upper bound on every canonical
Cartan coordinate. -/
theorem standard_carrier_le_leftScale_uniformizer_mapMatrix_iff_relativePosition
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ) (z : ℤ) :
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)).carrier ≤
      (leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z)
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)))).carrier ↔
      ∀ i, completedPseudoDiffOpDominantRelativePosition
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))) i + z ≤ 0 := by
  let L := standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)
  let M := mapCompletedPseudoDiffOpLatticeLinear
    (completedPseudoDiffOpMatrixLinearEquiv A) L
  let d := completedPseudoDiffOpDominantCartanData L M
  rw [← mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame]
  rw [mapCompletedPseudoDiffOpLatticeLinear_leftScale, d.map_right, d.map_left,
    leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const,
    ← standardCompletedPseudoDiffOpLatticeAtCoweight_zero,
    standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff]
  rw [standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
  simp only [Pi.add_apply]
  change (∀ i, d.coweight i + z ≤ 0) ↔ ∀ i,
    completedPseudoDiffOpDominantRelativePosition L M i + z ≤ 0
  rw [show d.coweight = completedPseudoDiffOpDominantRelativePosition L M from
    completedPseudoDiffOpDominantRelativePosition_eq L M d.frame d.coweight
      d.map_left d.map_right d.dominant]

end

end GaloisForLFunctions.HTGeometry.DiffOp

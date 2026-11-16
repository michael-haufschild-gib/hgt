import GaloisForLFunctions.CollectiveDiophantineGeometry.BoundedCoordinateElimination
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exact dimensions after coordinate elimination

Restricting a subspace to the discarded coordinates measures exactly the
dimension lost by coordinate elimination. For a matrix column space, this
is a difference of matrix ranks, without any column-independence premise.
-/

noncomputable section
namespace GaloisForLFunctions.CollectiveDiophantineGeometry
open Module

/-- Restriction to the coordinates discarded by elimination. -/
def discardedCoordinateMap {k : ℕ} (J : Finset (Fin k)) :
    (Fin k → ℚ) →ₗ[ℚ] ({j : Fin k // j ∉ J} → ℚ) where
  toFun v j := v j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinate elimination loses exactly the dimension seen on discarded coordinates. -/
theorem coordinateIntersection_finrank_add_projection {k : ℕ}
    (W : Submodule ℚ (Fin k → ℚ)) (J : Finset (Fin k)) :
    finrank ℚ ↥(W ⊓ coordinateSubspace J) +
      finrank ℚ ↥(W.map (discardedCoordinateMap J)) = finrank ℚ W := by
  let f := (discardedCoordinateMap J).comp W.subtype
  have hk : f.ker = (W ⊓ coordinateSubspace J).comap W.subtype := by
    ext x
    change (fun j : {j : Fin k // j ∉ J} => (x : Fin k → ℚ) j) = 0 ↔
      (x : Fin k → ℚ) ∈ W ∧ ∀ j, j ∉ J → (x : Fin k → ℚ) j = 0
    constructor
    · intro h
      exact ⟨x.property, fun j hj => congrFun h ⟨j, hj⟩⟩
    · rintro ⟨_, h⟩
      exact funext fun j => h j j.property
  have hr : f.range = W.map (discardedCoordinateMap J) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hk, hr, (Submodule.comapSubtypeEquivOfLe
    (show W ⊓ coordinateSubspace J ≤ W from inf_le_left)).finrank_eq] at h
  exact (Nat.add_comm _ _).trans h

/-- Rank difference measures the surviving coordinate-supported subspace. -/
theorem coordinateIntersection_finrank {k : ℕ}
    (W : Submodule ℚ (Fin k → ℚ)) (J : Finset (Fin k)) :
    finrank ℚ ↥(W ⊓ coordinateSubspace J) =
      finrank ℚ W - finrank ℚ ↥(W.map (discardedCoordinateMap J)) := by
  have h := coordinateIntersection_finrank_add_projection W J
  omega

/-- For a column space, deletion of rows gives the exact surviving dimension,
without any independence assumption on the original columns. -/
theorem columnSpace_coordinateIntersection_finrank {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℚ) (J : Finset (Fin k)) :
    finrank ℚ ↥(A.mulVecLin.range ⊓ coordinateSubspace J) =
      A.rank - (A.submatrix (fun j : {j : Fin k // j ∉ J} => j.val) id).rank := by
  rw [coordinateIntersection_finrank]
  have hr : A.mulVecLin.range.map (discardedCoordinateMap J) =
      (A.submatrix (fun j : {j : Fin k // j ∉ J} => j.val) id).mulVecLin.range := by
    ext y
    constructor
    · rintro ⟨x, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨A.mulVecLin v, ⟨v, rfl⟩, rfl⟩
  rw [hr]
  rfl

#print axioms coordinateIntersection_finrank_add_projection
#print axioms coordinateIntersection_finrank
#print axioms columnSpace_coordinateIntersection_finrank
end GaloisForLFunctions.CollectiveDiophantineGeometry

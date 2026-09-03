import GaloisForLFunctions.HTGeometry.DifferentialOperatorCompletedCartanBalance
import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpProjectiveEuclideanAction

/-!
# Exact Cartan balance from every lattice base point

The Cartan index of a semilinear lattice displacement equals the matrix Cartan character and is
therefore independent of the chosen lattice.  Operator matrices have zero character, so every
canonical variational action and every iterate is exactly balanced from every lattice base point.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K] {r : ℕ}

/-- Differential coefficient transport preserves the Cartan index. -/
theorem completedPseudoDiffOpCartanIndex_mapCoefficients
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpCartanIndex
        (mapCompletedPseudoDiffOpLattice σ hσ L)
        (mapCompletedPseudoDiffOpLattice σ hσ M) =
      completedPseudoDiffOpCartanIndex L M := by
  unfold completedPseudoDiffOpCartanIndex
  rw [completedPseudoDiffOpDominantRelativePosition_mapCoefficients]

/-- Simultaneous completed-skew semilinear transport preserves the Cartan index. -/
theorem completedPseudoDiffOpCartanIndex_semilinear
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ)
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpCartanIndex
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (mapCompletedPseudoDiffOpLattice σ hσ L))
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (mapCompletedPseudoDiffOpLattice σ hσ M)) =
      completedPseudoDiffOpCartanIndex L M := by
  rw [completedPseudoDiffOpCartanIndex_mapLinear,
    completedPseudoDiffOpCartanIndex_mapCoefficients]

/-- Semilinear displacement from any lattice has exactly the matrix Cartan character. -/
theorem completedPseudoDiffOpCartanIndex_semilinearDisplacement_eq_matrixCartanIndex
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ)
    (L : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpCartanIndex L
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (mapCompletedPseudoDiffOpLattice σ hσ L)) =
      completedPseudoDiffOpMatrixCartanIndex A := by
  let Z := standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)
  let T : CompletedPseudoDiffOpLattice K (Fin r) →
      CompletedPseudoDiffOpLattice K (Fin r) := fun N =>
    mapCompletedPseudoDiffOpLatticeLinear
      (completedPseudoDiffOpMatrixLinearEquiv A)
      (mapCompletedPseudoDiffOpLattice σ hσ N)
  have hTZ : T Z = mapCompletedPseudoDiffOpLatticeLinear
      (completedPseudoDiffOpMatrixLinearEquiv A) Z := by
    simp only [T, Z, map_standardCompletedPseudoDiffOpLattice]
  have hinv : completedPseudoDiffOpCartanIndex (T Z) (T L) =
      completedPseudoDiffOpCartanIndex Z L := by
    exact completedPseudoDiffOpCartanIndex_semilinear σ hσ A Z L
  have hcancel := completedPseudoDiffOpCartanIndex_add L Z L
  rw [completedPseudoDiffOpCartanIndex_self] at hcancel
  calc
    completedPseudoDiffOpCartanIndex L (T L) =
        completedPseudoDiffOpCartanIndex L Z +
          completedPseudoDiffOpCartanIndex Z (T L) :=
      completedPseudoDiffOpCartanIndex_add L Z (T L)
    _ = completedPseudoDiffOpCartanIndex L Z +
          (completedPseudoDiffOpCartanIndex Z (T Z) +
            completedPseudoDiffOpCartanIndex (T Z) (T L)) := by
      rw [completedPseudoDiffOpCartanIndex_add Z (T Z) (T L)]
    _ = completedPseudoDiffOpCartanIndex L Z +
          (completedPseudoDiffOpMatrixCartanIndex A +
            completedPseudoDiffOpCartanIndex Z L) := by
      rw [hinv, hTZ]
      rfl
    _ = completedPseudoDiffOpMatrixCartanIndex A := by omega

/-- Every invertible differential-operator matrix acts with exactly balanced Cartan displacement
from every completed valuation lattice. -/
theorem differentialOperatorSemilinearCartanBalance_everyLattice
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ)
    (L : CompletedPseudoDiffOpLattice K (Fin r)) :
    ∑ i, completedPseudoDiffOpDominantRelativePosition L
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv
            (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit A))
          (mapCompletedPseudoDiffOpLattice σ hσ L)) i = 0 := by
  change completedPseudoDiffOpCartanIndex L
      (mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpMatrixLinearEquiv
          (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit A))
        (mapCompletedPseudoDiffOpLattice σ hσ L)) = 0
  rw [completedPseudoDiffOpCartanIndex_semilinearDisplacement_eq_matrixCartanIndex]
  exact differentialOperatorMatrixCartanIndex_eq_zero A

end


end GaloisForLFunctions.HTGeometry.DiffOp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- The canonical variational action is exactly Cartan-balanced from every lattice base point. -/
theorem DifferentialFieldAut.variationalOreCartanBalance_everyLattice
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L
        (DiffOp.differentialVariationalLatticeSemilinearAction
          σ.toRingEquiv σ.deriv_comm
          (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b) L) i = 0 := by
  exact DiffOp.differentialOperatorSemilinearCartanBalance_everyLattice
    σ.toRingEquiv σ.deriv_comm
    (variationalOreOperatorMatrixUnit σ.fixes σ.deriv_comm b) L

/-- Every finite iterate of the canonical action is exactly Cartan-balanced from every lattice
base point. -/
theorem DifferentialFieldAut.variationalOreCartanBalance_pow_everyLattice
    (σ : DifferentialFieldAut C K) (n : ℕ)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L
        (DiffOp.differentialVariationalLatticeSemilinearAction
          (σ ^ n).toRingEquiv (σ ^ n).deriv_comm
          (variationalOreCompletedMatrixUnit (σ ^ n).fixes (σ ^ n).deriv_comm b) L) i = 0 :=
  (σ ^ n).variationalOreCartanBalance_everyLattice b L

end

end GaloisForLFunctions.HTGeometry

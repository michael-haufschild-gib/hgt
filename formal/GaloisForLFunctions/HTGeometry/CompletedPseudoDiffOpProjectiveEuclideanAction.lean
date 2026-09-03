import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpRelativePositionSymmetry
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingAction

/-!
# Vector-valued isometry of the projective completed-lattice action

Every finite completed-skew linear equivalence is represented by an invertible row-action matrix.
This lets coefficient automorphisms transport arbitrary Cartan frames.  Consequently both linear
and differential coefficient actions preserve the canonical dominant Cartan vector, its centered
Euclidean representative, and the descended projective vector-valued relative position exactly.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K] {r : ℕ}

/-- Row-action matrix of a finite completed-skew linear equivalence. -/
def completedPseudoDiffOpMatrixOfLinearEquiv
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K)) :
    Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K) :=
  fun i j => e (Pi.basisFun (CompletedPseudoDiffOp K) (Fin r) i) j

/-- The row-action matrix of a linear equivalence acts as that equivalence. -/
theorem vecMul_completedPseudoDiffOpMatrixOfLinearEquiv
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (v : Fin r → CompletedPseudoDiffOp K) :
    Matrix.vecMul v (completedPseudoDiffOpMatrixOfLinearEquiv e) = e v := by
  funext j
  let b := Pi.basisFun (CompletedPseudoDiffOp K) (Fin r)
  have hrepr : (∑ i, v i • b i) = v := by
    dsimp [b]
    simpa only [Pi.basisFun_repr] using
      (Pi.basisFun (CompletedPseudoDiffOp K) (Fin r)).sum_repr v
  calc
    Matrix.vecMul v (completedPseudoDiffOpMatrixOfLinearEquiv e) j =
        ∑ i, v i * e (b i) j := rfl
    _ = (∑ i, e (v i • b i)) j := by simp
    _ = e (∑ i, v i • b i) j := by rw [map_sum]
    _ = e v j := by rw [hrepr]

/-- The matrices of a linear equivalence and its inverse multiply to one. -/
theorem completedPseudoDiffOpMatrixOfLinearEquiv_mul_symm
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K)) :
    completedPseudoDiffOpMatrixOfLinearEquiv e *
        completedPseudoDiffOpMatrixOfLinearEquiv e.symm = 1 := by
  apply Matrix.ext
  intro i j
  have hvec : Matrix.vecMul
      (Matrix.vecMul (Pi.basisFun (CompletedPseudoDiffOp K) (Fin r) i)
        (completedPseudoDiffOpMatrixOfLinearEquiv e))
      (completedPseudoDiffOpMatrixOfLinearEquiv e.symm) =
      Pi.basisFun (CompletedPseudoDiffOp K) (Fin r) i := by
    rw [vecMul_completedPseudoDiffOpMatrixOfLinearEquiv,
      vecMul_completedPseudoDiffOpMatrixOfLinearEquiv]
    exact e.symm_apply_apply _
  rw [Matrix.vecMul_vecMul] at hvec
  have h := congrFun hvec j
  by_cases hij : i = j
  · subst j
    simpa [Matrix.vecMul] using h
  · simpa [Matrix.vecMul, hij] using h

/-- The inverse matrix also multiplies the original matrix to one. -/
theorem completedPseudoDiffOpMatrixOfLinearEquiv_symm_mul
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K)) :
    completedPseudoDiffOpMatrixOfLinearEquiv e.symm *
        completedPseudoDiffOpMatrixOfLinearEquiv e = 1 := by
  simpa using completedPseudoDiffOpMatrixOfLinearEquiv_mul_symm e.symm

/-- Every finite completed-skew linear equivalence gives an invertible row-action matrix. -/
def completedPseudoDiffOpMatrixUnitOfLinearEquiv
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K)) :
    (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ where
  val := completedPseudoDiffOpMatrixOfLinearEquiv e
  inv := completedPseudoDiffOpMatrixOfLinearEquiv e.symm
  val_inv := completedPseudoDiffOpMatrixOfLinearEquiv_mul_symm e
  inv_val := completedPseudoDiffOpMatrixOfLinearEquiv_symm_mul e

/-- Passing a finite linear equivalence to its matrix unit and back is exact. -/
theorem completedPseudoDiffOpMatrixLinearEquiv_matrixUnitOfLinearEquiv
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K)) :
    completedPseudoDiffOpMatrixLinearEquiv
      (completedPseudoDiffOpMatrixUnitOfLinearEquiv e) = e := by
  ext v j
  exact congrFun (vecMul_completedPseudoDiffOpMatrixOfLinearEquiv e v) j

/-- Differential coefficient transport preserves the canonical dominant Cartan vector. -/
theorem completedPseudoDiffOpDominantRelativePosition_mapCoefficients
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpDominantRelativePosition
        (mapCompletedPseudoDiffOpLattice σ hσ L)
        (mapCompletedPseudoDiffOpLattice σ hσ M) =
      completedPseudoDiffOpDominantRelativePosition L M := by
  let d := completedPseudoDiffOpDominantCartanData L M
  let A := completedPseudoDiffOpMatrixUnitOfLinearEquiv d.frame
  let e := completedPseudoDiffOpMatrixLinearEquiv
    (mapCompletedPseudoDiffOpMatrixUnit σ hσ A)
  have hA : completedPseudoDiffOpMatrixLinearEquiv A = d.frame :=
    completedPseudoDiffOpMatrixLinearEquiv_matrixUnitOfLinearEquiv d.frame
  have heL : mapCompletedPseudoDiffOpLatticeLinear e
      (mapCompletedPseudoDiffOpLattice σ hσ L) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
    rw [← mapCompletedPseudoDiffOpLattice_matrix σ hσ A L]
    rw [hA, d.map_left, map_standardCompletedPseudoDiffOpLattice]
  have heM : mapCompletedPseudoDiffOpLatticeLinear e
      (mapCompletedPseudoDiffOpLattice σ hσ M) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) d.coweight := by
    rw [← mapCompletedPseudoDiffOpLattice_matrix σ hσ A M]
    rw [hA, d.map_right, map_standardCompletedPseudoDiffOpLatticeAtCoweight]
  exact (completedPseudoDiffOpDominantRelativePosition_eq
    (mapCompletedPseudoDiffOpLattice σ hσ L)
    (mapCompletedPseudoDiffOpLattice σ hσ M)
    e d.coweight heL heM d.dominant).symm

/-- Simultaneous completed-skew linear transport preserves the Euclidean relative-position
point. -/
theorem completedPseudoDiffOpEuclideanRelativePositionPoint_mapLinear
    (g : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpEuclideanRelativePositionPoint
        (mapCompletedPseudoDiffOpLatticeLinear g L)
        (mapCompletedPseudoDiffOpLatticeLinear g M) =
      completedPseudoDiffOpEuclideanRelativePositionPoint L M := by
  apply Subtype.ext
  change WithLp.toLp 2 (centeredCoweight
      (completedPseudoDiffOpDominantRelativePosition
        (mapCompletedPseudoDiffOpLatticeLinear g L)
        (mapCompletedPseudoDiffOpLatticeLinear g M))) =
    WithLp.toLp 2 (centeredCoweight
      (completedPseudoDiffOpDominantRelativePosition L M))
  rw [completedPseudoDiffOpDominantRelativePosition_mapLinear]

/-- Differential coefficient transport preserves the Euclidean relative-position point. -/
theorem completedPseudoDiffOpEuclideanRelativePositionPoint_mapCoefficients
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpEuclideanRelativePositionPoint
        (mapCompletedPseudoDiffOpLattice σ hσ L)
        (mapCompletedPseudoDiffOpLattice σ hσ M) =
      completedPseudoDiffOpEuclideanRelativePositionPoint L M := by
  apply Subtype.ext
  change WithLp.toLp 2 (centeredCoweight
      (completedPseudoDiffOpDominantRelativePosition
        (mapCompletedPseudoDiffOpLattice σ hσ L)
        (mapCompletedPseudoDiffOpLattice σ hσ M))) =
    WithLp.toLp 2 (centeredCoweight
      (completedPseudoDiffOpDominantRelativePosition L M))
  rw [completedPseudoDiffOpDominantRelativePosition_mapCoefficients]

/-- Simultaneous completed-skew linear transport preserves projective vector-valued relative
position. -/
theorem differentialVariationalProjectiveEuclideanRelativePosition_mapLinear
    (g : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveEuclideanRelativePosition
        (mapDifferentialVariationalProjectiveBuildingCarrier g x)
        (mapDifferentialVariationalProjectiveBuildingCarrier g y) =
      differentialVariationalProjectiveEuclideanRelativePosition x y := by
  induction x using Quotient.inductionOn with
  | _ L =>
      induction y using Quotient.inductionOn with
      | _ M =>
          exact completedPseudoDiffOpEuclideanRelativePositionPoint_mapLinear g L M

/-- Simultaneous completed-skew linear transport preserves Euclidean vertex distance. -/
theorem differentialVariationalProjectiveEuclideanVertexDistance_mapLinear
    (g : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveEuclideanVertexDistance
        (mapDifferentialVariationalProjectiveBuildingCarrier g x)
        (mapDifferentialVariationalProjectiveBuildingCarrier g y) =
      differentialVariationalProjectiveEuclideanVertexDistance x y := by
  unfold differentialVariationalProjectiveEuclideanVertexDistance
  rw [differentialVariationalProjectiveEuclideanRelativePosition_mapLinear]

/-- Differential coefficient transport preserves projective vector-valued relative position. -/
theorem differentialVariationalProjectiveEuclideanRelativePosition_mapCoefficients
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveEuclideanRelativePosition
        (mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ x)
        (mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ y) =
      differentialVariationalProjectiveEuclideanRelativePosition x y := by
  induction x using Quotient.inductionOn with
  | _ L =>
      induction y using Quotient.inductionOn with
      | _ M =>
          exact completedPseudoDiffOpEuclideanRelativePositionPoint_mapCoefficients σ hσ L M

/-- Differential coefficient transport preserves Euclidean vertex distance. -/
theorem differentialVariationalProjectiveEuclideanVertexDistance_mapCoefficients
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveEuclideanVertexDistance
        (mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ x)
        (mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ y) =
      differentialVariationalProjectiveEuclideanVertexDistance x y := by
  unfold differentialVariationalProjectiveEuclideanVertexDistance
  rw [differentialVariationalProjectiveEuclideanRelativePosition_mapCoefficients]

/-- Every literal differential semilinear action preserves the complete vector-valued projective
relative position. -/
theorem differentialVariationalProjectiveEuclideanRelativePosition_semilinearAction
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ)
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveEuclideanRelativePosition
        (differentialVariationalProjectiveSemilinearAction σ hσ A x)
        (differentialVariationalProjectiveSemilinearAction σ hσ A y) =
      differentialVariationalProjectiveEuclideanRelativePosition x y := by
  simp only [differentialVariationalProjectiveSemilinearAction,
    mapDifferentialVariationalProjectiveBuildingCarrierMatrix]
  rw [differentialVariationalProjectiveEuclideanRelativePosition_mapLinear,
    differentialVariationalProjectiveEuclideanRelativePosition_mapCoefficients]

/-- Every literal differential semilinear action preserves Euclidean vertex distance. -/
theorem differentialVariationalProjectiveEuclideanVertexDistance_semilinearAction
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ)
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveEuclideanVertexDistance
        (differentialVariationalProjectiveSemilinearAction σ hσ A x)
        (differentialVariationalProjectiveSemilinearAction σ hσ A y) =
      differentialVariationalProjectiveEuclideanVertexDistance x y := by
  unfold differentialVariationalProjectiveEuclideanVertexDistance
  rw [differentialVariationalProjectiveEuclideanRelativePosition_semilinearAction]

end

end GaloisForLFunctions.HTGeometry.DiffOp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- The canonical variational Ore action preserves the full projective Euclidean relative-position
vector in every finite operator basis. -/
theorem DifferentialFieldAut.projectiveBuildingAction_euclideanRelativePosition
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    DiffOp.differentialVariationalProjectiveEuclideanRelativePosition
        (σ.projectiveBuildingAction b x) (σ.projectiveBuildingAction b y) =
      DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y := by
  exact DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_semilinearAction
    σ.toRingEquiv σ.deriv_comm (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b) x y

/-- The canonical variational Ore action preserves Euclidean distance between projective
lattice vertices in every finite operator basis. -/
theorem DifferentialFieldAut.projectiveBuildingAction_euclideanVertexDistance
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
        (σ.projectiveBuildingAction b x) (σ.projectiveBuildingAction b y) =
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y := by
  unfold DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
  rw [σ.projectiveBuildingAction_euclideanRelativePosition]

end

end GaloisForLFunctions.HTGeometry

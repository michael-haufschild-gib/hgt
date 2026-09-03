import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpProjectiveEuclideanIsometry

/-!
# Euclidean basis-change isometries of the differential variational building

Invertible completed-skew matrix transport is packaged as a literal Euclidean `IsometryEquiv`.
The exact twisted basis-change identity then becomes conjugacy of the canonical actions by this
isometry.  This is the metric-level generator-independence statement in Theorem A.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K] {r : ℕ}

/-- Every invertible completed-skew matrix acts by a Euclidean isometry equivalence on projective
lattice vertices. -/
noncomputable def differentialVariationalProjectiveMatrixEuclideanIsometryEquiv
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ) :
    @IsometryEquiv
      (DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
      (DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
      differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace :=
  @IsometryEquiv.mk
    (DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
    differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
    { toFun := mapDifferentialVariationalProjectiveBuildingCarrierMatrix A
      invFun := mapDifferentialVariationalProjectiveBuildingCarrierMatrix A⁻¹
      left_inv := fun x => by
        rw [mapDifferentialVariationalProjectiveBuildingCarrierMatrix_mul,
          mul_inv_cancel, mapDifferentialVariationalProjectiveBuildingCarrierMatrix_one]
      right_inv := fun x => by
        rw [mapDifferentialVariationalProjectiveBuildingCarrierMatrix_mul,
          inv_mul_cancel, mapDifferentialVariationalProjectiveBuildingCarrierMatrix_one] }
    (by
      intro x y
      simp only [edist_dist]
      change ENNReal.ofReal
          (differentialVariationalProjectiveEuclideanVertexDistance
            (mapDifferentialVariationalProjectiveBuildingCarrierMatrix A x)
            (mapDifferentialVariationalProjectiveBuildingCarrierMatrix A y)) =
        ENNReal.ofReal (differentialVariationalProjectiveEuclideanVertexDistance x y)
      rw [mapDifferentialVariationalProjectiveBuildingCarrierMatrix]
      rw [differentialVariationalProjectiveEuclideanVertexDistance_mapLinear])

@[simp]
theorem differentialVariationalProjectiveMatrixEuclideanIsometryEquiv_apply
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ)
    (x : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveMatrixEuclideanIsometryEquiv A x =
      mapDifferentialVariationalProjectiveBuildingCarrierMatrix A x :=
  rfl

end


end GaloisForLFunctions.HTGeometry.DiffOp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Completed transition between two operator bases, as a Euclidean isometry equivalence. -/
noncomputable def variationalOreCompletedBasisTransitionEuclideanIsometryEquiv
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    @IsometryEquiv
      (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
      (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
      DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace :=
  DiffOp.differentialVariationalProjectiveMatrixEuclideanIsometryEquiv
    (variationalOreCompletedBasisTransition b c)

/-- Canonical Euclidean actions in two finite operator bases are conjugate by their literal
Euclidean transition isometry. -/
theorem DifferentialFieldAut.projectiveBuildingEuclideanIsometryEquiv_changeBasis
    (σ : DifferentialFieldAut C K)
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    @IsometryEquiv.trans
        (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
        (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
        (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
        DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        (σ.projectiveBuildingEuclideanIsometryEquiv c)
        (variationalOreCompletedBasisTransitionEuclideanIsometryEquiv b c) =
      @IsometryEquiv.trans
        (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
        (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
        (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
        DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        (variationalOreCompletedBasisTransitionEuclideanIsometryEquiv b c)
        (σ.projectiveBuildingEuclideanIsometryEquiv b) := by
  apply @IsometryEquiv.ext
    (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
    DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
  intro x
  change DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
      (variationalOreCompletedBasisTransition b c)
      (σ.projectiveBuildingAction c x) =
    σ.projectiveBuildingAction b
      (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
        (variationalOreCompletedBasisTransition b c) x)
  exact variationalOreProjectiveBuildingAction_changeBasis σ.fixes σ.deriv_comm b c x

end

end GaloisForLFunctions.HTGeometry

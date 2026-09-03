import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpEuclideanComplete
import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpProjectiveEuclideanAction

/-!
# Euclidean isometries of the differential-variational projective lattice space

This file packages the previously proved exact distance invariance as literal `Isometry` and
`IsometryEquiv` values for the named Euclidean metric.  No replacement metric or auxiliary
hypothesis is introduced.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K] {r : ℕ}

/-- Every literal completed-skew semilinear projective action is an isometry for the exact
Euclidean vertex metric. -/
theorem differentialVariationalProjectiveSemilinearAction_euclideanIsometry
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ) :
    @Isometry _ _
      differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      (differentialVariationalProjectiveSemilinearAction σ hσ A) := by
  intro x y
  simp only [edist_dist]
  change ENNReal.ofReal
      (differentialVariationalProjectiveEuclideanVertexDistance
        (differentialVariationalProjectiveSemilinearAction σ hσ A x)
        (differentialVariationalProjectiveSemilinearAction σ hσ A y)) =
    ENNReal.ofReal (differentialVariationalProjectiveEuclideanVertexDistance x y)
  rw [differentialVariationalProjectiveEuclideanVertexDistance_semilinearAction]

end

end GaloisForLFunctions.HTGeometry.DiffOp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Canonical differential-field automorphisms act isometrically on the exact Euclidean projective
lattice space in every finite operator basis. -/
theorem DifferentialFieldAut.projectiveBuildingAction_euclideanIsometry
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    @Isometry _ _
      DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      (σ.projectiveBuildingAction b) := by
  intro x y
  simp only [edist_dist]
  change ENNReal.ofReal
      (DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
        (σ.projectiveBuildingAction b x) (σ.projectiveBuildingAction b y)) =
    ENNReal.ofReal (DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y)
  rw [σ.projectiveBuildingAction_euclideanVertexDistance]

/-- The canonical action together with the inverse-automorphism action is a genuine Euclidean
isometry equivalence. -/
noncomputable def DifferentialFieldAut.projectiveBuildingEuclideanIsometryEquiv
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    @IsometryEquiv
      (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
      (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
      DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace :=
  @IsometryEquiv.mk
    (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
    DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
    (σ.projectiveBuildingEquiv b)
    (σ.projectiveBuildingAction_euclideanIsometry b)

@[simp]
theorem DifferentialFieldAut.projectiveBuildingEuclideanIsometryEquiv_apply
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    σ.projectiveBuildingEuclideanIsometryEquiv b x = σ.projectiveBuildingAction b x :=
  rfl

/-- Chronological multiplication of differential automorphisms is composition of their Euclidean
isometry equivalences. -/
theorem DifferentialFieldAut.projectiveBuildingEuclideanIsometryEquiv_mul
    (σ τ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    projectiveBuildingEuclideanIsometryEquiv (σ * τ) b =
      @IsometryEquiv.trans
        (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
        (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
        (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
        DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        (projectiveBuildingEuclideanIsometryEquiv σ b)
        (projectiveBuildingEuclideanIsometryEquiv τ b) := by
  apply @IsometryEquiv.ext
    (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
    DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
  intro x
  simp only [projectiveBuildingEuclideanIsometryEquiv_apply]
  exact projectiveBuildingAction_mul σ τ b x

/-- The identity differential automorphism gives the identity Euclidean isometry equivalence. -/
theorem DifferentialFieldAut.projectiveBuildingEuclideanIsometryEquiv_one
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    projectiveBuildingEuclideanIsometryEquiv (1 : DifferentialFieldAut C K) b =
      @IsometryEquiv.refl
        (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
        DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace := by
  apply @IsometryEquiv.ext
    (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
    DiffOp.differentialVariationalProjectiveEuclideanMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
  intro x
  rw [projectiveBuildingEuclideanIsometryEquiv_apply]
  exact projectiveBuildingAction_one b x

end

end GaloisForLFunctions.HTGeometry

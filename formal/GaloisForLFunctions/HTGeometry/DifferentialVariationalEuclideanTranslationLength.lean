import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpProjectiveEuclideanIsometry
import GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableNet

/-!
# Intrinsic scalar Euclidean translation length

Euclidean orbit distance is a nonnegative subadditive gauge on the differential-automorphism
group.  Fekete's lemma therefore gives an actual normalized scalar limit.  A uniform two-base-point
bound and exact basis-transition conjugacy prove that limit is independent of both lattice base
point and finite operator basis.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Euclidean displacement from a fixed projective lattice vertex, as a subadditive group gauge. -/
noncomputable def differentialVariationalEuclideanOrbitGauge
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    SubadditiveClockGauge (DifferentialFieldAut C K) where
  cost σ := DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
    x (σ.projectiveBuildingAction b x)
  cost_nonneg σ := DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_nonneg _ _
  cost_one := by rw [DifferentialFieldAut.projectiveBuildingAction_one,
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_self]
  cost_mul_le σ τ := by
    rw [DifferentialFieldAut.projectiveBuildingAction_mul]
    calc
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
          (τ.projectiveBuildingAction b (σ.projectiveBuildingAction b x)) ≤
        DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
            (τ.projectiveBuildingAction b x) +
          DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
            (τ.projectiveBuildingAction b x)
            (τ.projectiveBuildingAction b (σ.projectiveBuildingAction b x)) :=
        DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_triangle _ _ _
      _ = DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
            (τ.projectiveBuildingAction b x) +
          DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
            (σ.projectiveBuildingAction b x) := by
        rw [τ.projectiveBuildingAction_euclideanVertexDistance]
      _ = DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
            (σ.projectiveBuildingAction b x) +
          DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
            (τ.projectiveBuildingAction b x) := add_comm _ _

/-- Stable scalar Euclidean speed of the variational action. -/
noncomputable def differentialVariationalEuclideanTranslationLength
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) : ℝ :=
  (differentialVariationalEuclideanOrbitGauge b x).translationLength σ

/-- Normalized Euclidean orbit distance converges to the scalar translation length. -/
theorem tendsto_differentialVariationalEuclidean_normalizedOrbitDistance
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    Filter.Tendsto
      (fun n : ℕ =>
        DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
            ((σ ^ n).projectiveBuildingAction b x) / n)
      Filter.atTop (nhds (differentialVariationalEuclideanTranslationLength b x σ)) := by
  exact (differentialVariationalEuclideanOrbitGauge b x).tendsto_normalizedOrbitCost σ

/-- Changing the lattice base point changes every finite orbit displacement by at most twice the
distance between the base points. -/
theorem differentialVariationalEuclideanOrbitGauge_cost_base_le
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    (differentialVariationalEuclideanOrbitGauge b x).cost σ ≤
      (differentialVariationalEuclideanOrbitGauge b y).cost σ +
        2 * DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y := by
  change DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
      (σ.projectiveBuildingAction b x) ≤
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance y
        (σ.projectiveBuildingAction b y) +
      2 * DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y
  calc
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
        (σ.projectiveBuildingAction b x) ≤
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y +
        DiffOp.differentialVariationalProjectiveEuclideanVertexDistance y
          (σ.projectiveBuildingAction b x) :=
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_triangle _ _ _
    _ ≤ DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y +
        (DiffOp.differentialVariationalProjectiveEuclideanVertexDistance y
            (σ.projectiveBuildingAction b y) +
          DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
            (σ.projectiveBuildingAction b y) (σ.projectiveBuildingAction b x)) := by
      gcongr
      exact DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_triangle _ _ _
    _ = DiffOp.differentialVariationalProjectiveEuclideanVertexDistance y
          (σ.projectiveBuildingAction b y) +
        2 * DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y := by
      rw [σ.projectiveBuildingAction_euclideanVertexDistance,
        DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_comm y x]
      ring

/-- Orbit gauges from two lattice base points differ by a uniform bounded overhead. -/
noncomputable def differentialVariationalEuclideanOrbitGauge_boundedComparison
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    SubadditiveClockGauge.BoundedComparison
      (differentialVariationalEuclideanOrbitGauge b x)
      (differentialVariationalEuclideanOrbitGauge b y) where
  forwardOverhead := 2 * DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y
  backwardOverhead := 2 * DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y
  cost_le_forward := differentialVariationalEuclideanOrbitGauge_cost_base_le b x y
  cost_le_backward := by
    intro σ
    simpa only [DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_comm x y] using
      differentialVariationalEuclideanOrbitGauge_cost_base_le b y x σ

/-- Scalar Euclidean translation length is independent of the lattice base point. -/
theorem differentialVariationalEuclideanTranslationLength_base_independent
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    differentialVariationalEuclideanTranslationLength b x σ =
      differentialVariationalEuclideanTranslationLength b y σ := by
  exact (differentialVariationalEuclideanOrbitGauge_boundedComparison b x y).translationLength_eq σ

/-- Transporting the base point by the completed transition matrix identifies finite orbit costs
in two operator bases exactly. -/
theorem differentialVariationalEuclideanOrbitGauge_cost_changeBasis
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    (differentialVariationalEuclideanOrbitGauge b
      (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
        (variationalOreCompletedBasisTransition b c) x)).cost σ =
      (differentialVariationalEuclideanOrbitGauge c x).cost σ := by
  change DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
      (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
        (variationalOreCompletedBasisTransition b c) x)
      (σ.projectiveBuildingAction b
        (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
          (variationalOreCompletedBasisTransition b c) x)) =
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
      (σ.projectiveBuildingAction c x)
  unfold DifferentialFieldAut.projectiveBuildingAction
  rw [← variationalOreProjectiveBuildingAction_changeBasis
    σ.fixes σ.deriv_comm b c x]
  unfold DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
  exact DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_mapLinear
    _ x (σ.projectiveBuildingAction c x)

/-- Basis-transition orbit gauges agree with zero overhead. -/
noncomputable def differentialVariationalEuclideanOrbitGauge_changeBasisComparison
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    SubadditiveClockGauge.BoundedComparison
      (differentialVariationalEuclideanOrbitGauge b
        (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
          (variationalOreCompletedBasisTransition b c) x))
      (differentialVariationalEuclideanOrbitGauge c x) where
  forwardOverhead := 0
  backwardOverhead := 0
  cost_le_forward := fun σ => by
    rw [differentialVariationalEuclideanOrbitGauge_cost_changeBasis b c x σ, add_zero]
  cost_le_backward := fun σ => by
    rw [differentialVariationalEuclideanOrbitGauge_cost_changeBasis b c x σ, add_zero]

/-- Scalar Euclidean translation length is independent of every finite operator-basis choice and
of both chosen lattice base points. -/
theorem differentialVariationalEuclideanTranslationLength_basis_independent
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    differentialVariationalEuclideanTranslationLength b x σ =
      differentialVariationalEuclideanTranslationLength c y σ := by
  rw [differentialVariationalEuclideanTranslationLength_base_independent b x
    (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
      (variationalOreCompletedBasisTransition b c) y) σ]
  exact (differentialVariationalEuclideanOrbitGauge_changeBasisComparison b c y).translationLength_eq σ

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.DifferentialVariationalRankOneBuilding
import GaloisForLFunctions.HTGeometry.DifferentialVariationalRankOneAction
import GaloisForLFunctions.HTGeometry.DifferentialVariationalCartanTranslationNorm

/-!
# Exact rank-one differential variational phase

The projective completed-lattice carrier in rank one is a singleton.  Hence every canonical
differential-field action fixes its unique vertex, every orbit displacement vanishes, and both
the intrinsic Cartan vector and scalar Euclidean speed are zero.  This is the full geometric
type-`A₀` no-displacement law, not only its free-field order corollary.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Boundedness of one projective Euclidean variational orbit. -/
def DifferentialVariationalEuclideanOrbitBounded
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ,
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
      ((σ ^ n).projectiveBuildingAction b x) ≤ B

/-- Existence of a fixed projective completed-lattice vertex. -/
def DifferentialVariationalHasFixedVertex
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (σ : DifferentialFieldAut C K) : Prop :=
  ∃ x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r),
    σ.projectiveBuildingAction b x = x

/-- Every rank-one canonical variational action fixes every projective lattice vertex. -/
theorem differentialVariationalProjectiveBuildingAction_finOne_fixed
    (b : Module.Basis (Fin 1) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin 1))
    (σ : DifferentialFieldAut C K) :
    σ.projectiveBuildingAction b x = x :=
  σ.projectiveBuildingAction_rankOne b x

/-- Every displacement in a rank-one orbit is exactly zero. -/
theorem differentialVariationalEuclideanOrbitDistance_finOne_eq_zero
    (b : Module.Basis (Fin 1) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin 1))
    (σ : DifferentialFieldAut C K) (n : ℕ) :
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
      ((σ ^ n).projectiveBuildingAction b x) = 0 := by
  rw [differentialVariationalProjectiveBuildingAction_finOne_fixed]
  exact DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_self x

/-- The intrinsic rank-one Cartan translation vector vanishes identically. -/
theorem differentialVariationalCartanTranslationVector_finOne_eq_zero
    (b : Module.Basis (Fin 1) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin 1))
    (σ : DifferentialFieldAut C K) :
    differentialVariationalCartanTranslationVector b x σ = 0 := by
  funext i
  fin_cases i
  have hsum := differentialVariationalCartanTranslationVector_sum_eq_zero b x σ
  simpa using hsum

/-- Every rank-one variational action has zero scalar Euclidean translation speed. -/
theorem differentialVariationalEuclideanTranslationLength_finOne_eq_zero
    (b : Module.Basis (Fin 1) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin 1))
    (σ : DifferentialFieldAut C K) :
    differentialVariationalEuclideanTranslationLength b x σ = 0 := by
  rw [differentialVariationalEuclideanTranslationLength_eq_zero_iff_cartanVector_eq_zero]
  exact differentialVariationalCartanTranslationVector_finOne_eq_zero b x σ

/-- Every rank-one projective variational orbit is bounded, with bound zero. -/
theorem differentialVariationalEuclideanOrbitBounded_finOne
    (b : Module.Basis (Fin 1) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin 1))
    (σ : DifferentialFieldAut C K) :
    DifferentialVariationalEuclideanOrbitBounded b x σ := by
  refine ⟨0, fun n => ?_⟩
  rw [differentialVariationalEuclideanOrbitDistance_finOne_eq_zero]

/-- Every rank-one canonical action has a fixed projective valuation-lattice vertex. -/
theorem differentialVariationalHasFixedVertex_finOne
    (b : Module.Basis (Fin 1) (DiffOp K) (VariationalOreModule C K))
    (σ : DifferentialFieldAut C K) :
    DifferentialVariationalHasFixedVertex b σ := by
  let x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin 1) :=
    Quotient.mk
      (DiffOp.completedPseudoDiffOpLatticeLeftHomothetySetoid
        (K := K) (ι := Fin 1))
      (DiffOp.standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin 1))
  exact ⟨x, differentialVariationalProjectiveBuildingAction_finOne_fixed b x σ⟩

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingMetricSpace
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingAction

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

namespace DifferentialFieldAut

/-- Canonical variational action bundled as an isometric equivalence for the projective
interleaving metric. -/
noncomputable def projectiveBuildingInterleavingIsometryEquiv
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r) ≃ᵢ
      DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r) :=
  IsometryEquiv.mk (σ.projectiveBuildingEquiv b) (by
    rw [isometry_iff_dist_eq]
    intro x y
    rw [DiffOp.dist_eq_differentialVariationalProjectiveInterleavingDistance,
      DiffOp.dist_eq_differentialVariationalProjectiveInterleavingDistance]
    exact_mod_cast σ.projectiveBuildingAction_interleavingDistance b x y)

@[simp] theorem projectiveBuildingInterleavingIsometryEquiv_apply
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    σ.projectiveBuildingInterleavingIsometryEquiv b x =
      σ.projectiveBuildingAction b x := rfl

theorem projectiveBuildingInterleavingIsometryEquiv_mul
    (σ τ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    projectiveBuildingInterleavingIsometryEquiv (σ * τ) b =
      (projectiveBuildingInterleavingIsometryEquiv σ b).trans
        (projectiveBuildingInterleavingIsometryEquiv τ b) := by
  ext x
  exact projectiveBuildingAction_mul σ τ b x

@[simp] theorem projectiveBuildingInterleavingIsometryEquiv_one
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    projectiveBuildingInterleavingIsometryEquiv
        (1 : DifferentialFieldAut C K) b = IsometryEquiv.refl _ := by
  ext x
  exact projectiveBuildingAction_one b x

end DifferentialFieldAut

end

end GaloisForLFunctions.HTGeometry

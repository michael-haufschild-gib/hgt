import GaloisForLFunctions.RHTower.SemilocalProjectionPhasePolarization
import GaloisForLFunctions.HTGeometry.DoubledParityClock
import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra

open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The two-level carrier for the closed projection-phase realization. -/
abbrev ProjectionPhaseCarrier := WithLp 2 (ℂ × ℂ)

abbrev ProjectionPhaseEnd := ProjectionPhaseCarrier →L[ℂ] ProjectionPhaseCarrier

/-- The Pauli-X tangent on the two-level carrier. -/
def projectionPhaseX : ProjectionPhaseEnd :=
  HTGeometry.doubledParityClock (1 : ℂ →L[ℂ] ℂ)

/-- The Pauli-Z grading from which the idempotent projection is formed. -/
def projectionPhaseZ : ProjectionPhaseEnd :=
  HTGeometry.doubledOddObservable (1 : ℂ →L[ℂ] ℂ)

theorem projectionPhaseX_sq : projectionPhaseX * projectionPhaseX = 1 := by
  simpa only [projectionPhaseX, pow_two] using
    HTGeometry.doubledParityClock_sq (1 : ℂ →L[ℂ] ℂ) (by simp)

theorem projectionPhaseZ_sq : projectionPhaseZ * projectionPhaseZ = 1 := by
  ext x
  apply (WithLp.equiv 2 (ℂ × ℂ)).injective
  apply Prod.ext <;> simp [projectionPhaseZ, mul_apply_eq_comp]

theorem projectionPhaseX_mul_Z_eq_neg :
    projectionPhaseX * projectionPhaseZ = -(projectionPhaseZ * projectionPhaseX) := by
  ext x
  apply (WithLp.equiv 2 (ℂ × ℂ)).injective
  apply Prod.ext <;> simp [projectionPhaseX, projectionPhaseZ, mul_apply_eq_comp]

theorem projectionPhaseX_isSelfAdjoint : IsSelfAdjoint projectionPhaseX := by
  exact HTGeometry.doubledParityClock_isSelfAdjoint (1 : ℂ →L[ℂ] ℂ) (by simp)

theorem projectionPhaseZ_isSelfAdjoint : IsSelfAdjoint projectionPhaseZ := by
  exact HTGeometry.doubledOddObservable_isSelfAdjoint (1 : ℂ →L[ℂ] ℂ) (by simp)

/-- The upper-sector projection `(1 + Z) / 2`. -/
def projectionPhaseProjection : ProjectionPhaseEnd :=
  ((2 : ℂ)⁻¹) • (1 + projectionPhaseZ)

theorem projectionPhaseProjection_apply (x : ProjectionPhaseCarrier) :
    projectionPhaseProjection x = WithLp.toLp 2 (x.fst, 0) := by
  apply (WithLp.equiv 2 (ℂ × ℂ)).injective
  apply Prod.ext
  · simp [projectionPhaseProjection, projectionPhaseZ]
    field_simp
    ring
  · simp [projectionPhaseProjection, projectionPhaseZ]

theorem projectionPhaseProjection_sq :
    projectionPhaseProjection * projectionPhaseProjection = projectionPhaseProjection := by
  ext x
  change projectionPhaseProjection (projectionPhaseProjection x) = projectionPhaseProjection x
  rw [projectionPhaseProjection_apply (projectionPhaseProjection x),
    projectionPhaseProjection_apply x]
  rfl

theorem projectionPhaseProjection_isSelfAdjoint :
    IsSelfAdjoint projectionPhaseProjection := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold projectionPhaseProjection
  change ContinuousLinearMap.adjoint
      (((2 : ℂ)⁻¹) • (1 + projectionPhaseZ)) = _
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ, map_add,
    ContinuousLinearMap.adjoint_one,
    projectionPhaseZ_isSelfAdjoint.adjoint_eq]
  change star ((2 : ℂ)⁻¹) • (1 + projectionPhaseZ) =
    ((2 : ℂ)⁻¹) • (1 + projectionPhaseZ)
  rw [show star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ by norm_num]

/-- Pauli-X is a nonzero self-adjoint tangent at the upper-sector projection. -/
theorem projectionPhaseX_tangent_projection :
    projectionPhaseX * projectionPhaseProjection +
      projectionPhaseProjection * projectionPhaseX = projectionPhaseX := by
  unfold projectionPhaseProjection
  rw [mul_smul_comm, smul_mul_assoc]
  have hsum : projectionPhaseX * projectionPhaseZ +
      projectionPhaseZ * projectionPhaseX = 0 := by
    calc
      projectionPhaseX * projectionPhaseZ + projectionPhaseZ * projectionPhaseX =
          -(projectionPhaseZ * projectionPhaseX) + projectionPhaseZ * projectionPhaseX :=
        congrArg (fun z : ProjectionPhaseEnd => z + projectionPhaseZ * projectionPhaseX)
          projectionPhaseX_mul_Z_eq_neg
      _ = 0 := by
        ext x
        simp
  have hbody : projectionPhaseX * (1 + projectionPhaseZ) +
      (1 + projectionPhaseZ) * projectionPhaseX = (2 : ℂ) • projectionPhaseX := by
    calc
      projectionPhaseX * (1 + projectionPhaseZ) +
          (1 + projectionPhaseZ) * projectionPhaseX =
          projectionPhaseX + (projectionPhaseX * projectionPhaseZ +
            projectionPhaseZ * projectionPhaseX) + projectionPhaseX := by
        noncomm_ring
      _ = projectionPhaseX + projectionPhaseX := by rw [hsum]; simp
      _ = (2 : ℂ) • projectionPhaseX := by module
  calc
    ((2 : ℂ)⁻¹) • (projectionPhaseX * (1 + projectionPhaseZ)) +
        ((2 : ℂ)⁻¹) • ((1 + projectionPhaseZ) * projectionPhaseX) =
        ((2 : ℂ)⁻¹) •
          (projectionPhaseX * (1 + projectionPhaseZ) +
            (1 + projectionPhaseZ) * projectionPhaseX) :=
      (smul_add _ _ _).symm
    _ = projectionPhaseX := by
      rw [hbody, smul_smul]
      norm_num

/-- The canonical quarter-turn of the concrete projection tangent. -/
def projectionPhaseY : ProjectionPhaseEnd :=
  projectionPhaseRotation projectionPhaseProjection projectionPhaseX

theorem projectionPhaseY_sq : projectionPhaseY * projectionPhaseY = 1 := by
  unfold projectionPhaseY
  rw [projectionPhaseRotation_sq_eq_tangent_sq
    projectionPhaseProjection projectionPhaseX projectionPhaseProjection_sq
    projectionPhaseProjection_isSelfAdjoint.adjoint_eq
    projectionPhaseX_isSelfAdjoint.adjoint_eq projectionPhaseX_tangent_projection]
  exact projectionPhaseX_sq

theorem projectionPhaseX_Y_anticommutes :
    projectionPhaseX * projectionPhaseY + projectionPhaseY * projectionPhaseX = 0 := by
  unfold projectionPhaseY
  exact projectionTangent_anticommutes_phaseRotation
    projectionPhaseProjection projectionPhaseX projectionPhaseProjection_sq
    projectionPhaseProjection_isSelfAdjoint.adjoint_eq
    projectionPhaseX_isSelfAdjoint.adjoint_eq projectionPhaseX_tangent_projection

/-- Fully closed, nonzero `D = 1`, `N = 2` realization of phase-polarized projection geometry.
It formalizes the algebraic mechanism; it makes no claim that this two-level carrier is the
missing semilocal Sonin source. -/
def projectionPhaseD1N2 : SuperPoincare.D1N2 ProjectionPhaseEnd where
  supercharge0 := projectionPhaseX
  supercharge1 := projectionPhaseY
  momentum := 1
  supercharge0_sq := projectionPhaseX_sq
  supercharge1_sq := projectionPhaseY_sq
  mixed_anticommutator := projectionPhaseX_Y_anticommutes

end RHTower

import GaloisForLFunctions.RHTower.SuperPoincareProjectionPhase
import GaloisForLFunctions.HTGeometry.SuperPoincareChiral

/-!
# Concrete projection-family supersymmetry

This module supplies the finite-dimensional infrastructure which the semilocal programme would
need from a genuine analytic source: an idempotent curve, its normal tangent, and its chiral
BRST realization.  The curve is deliberately an oblique-idempotent shear, rather than a family
of orthogonal projections.  Thus it is a closed algebraic model and not a claim about the
semilocal Sonin projections.
-/

open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The lower-to-upper normal corner of the concrete Pauli-X tangent. -/
def projectionPhaseNormal : ProjectionPhaseEnd :=
  projectionNormalCorner projectionPhaseProjection projectionPhaseX

theorem projectionPhaseProjection_mul_complement :
    projectionPhaseProjection * (1 - projectionPhaseProjection) = 0 := by
  rw [mul_sub, mul_one, projectionPhaseProjection_sq, sub_self]

theorem projectionPhaseProjection_mul_normal :
    projectionPhaseProjection * projectionPhaseNormal = 0 := by
  unfold projectionPhaseNormal projectionNormalCorner
  rw [mul_assoc (1 - projectionPhaseProjection) projectionPhaseX projectionPhaseProjection]
  rw [← mul_assoc projectionPhaseProjection (1 - projectionPhaseProjection)
    (projectionPhaseX * projectionPhaseProjection)]
  rw [projectionPhaseProjection_mul_complement, zero_mul]

theorem projectionPhaseNormal_mul_projection :
    projectionPhaseNormal * projectionPhaseProjection = projectionPhaseNormal := by
  unfold projectionPhaseNormal projectionNormalCorner
  calc
    ((1 - projectionPhaseProjection) * projectionPhaseX * projectionPhaseProjection) *
        projectionPhaseProjection =
        (1 - projectionPhaseProjection) * projectionPhaseX *
          (projectionPhaseProjection * projectionPhaseProjection) := by
      simp only [mul_assoc]
    _ = (1 - projectionPhaseProjection) * projectionPhaseX * projectionPhaseProjection := by
      rw [projectionPhaseProjection_sq]

/-- The concrete normal corner is a nilpotent BRST charge. -/
theorem projectionPhaseNormal_sq : projectionPhaseNormal * projectionPhaseNormal = 0 := by
  exact projectionNormalCorner_sq_eq_zero projectionPhaseProjection projectionPhaseX
    projectionPhaseProjection_sq

/-- A norm-differentiable family of idempotents based at the concrete projection.

For nonzero parameter this is generally an oblique idempotent, not an orthogonal projection. -/
def projectionPhaseShearFamily (t : ℝ) : ProjectionPhaseEnd :=
  projectionPhaseProjection + (t : ℂ) • projectionPhaseNormal

theorem projectionPhaseShearFamily_idempotent (t : ℝ) :
    projectionPhaseShearFamily t * projectionPhaseShearFamily t = projectionPhaseShearFamily t := by
  unfold projectionPhaseShearFamily
  calc
    (projectionPhaseProjection + (t : ℂ) • projectionPhaseNormal) *
        (projectionPhaseProjection + (t : ℂ) • projectionPhaseNormal) =
        projectionPhaseProjection * projectionPhaseProjection +
          projectionPhaseProjection * ((t : ℂ) • projectionPhaseNormal) +
          ((t : ℂ) • projectionPhaseNormal) * projectionPhaseProjection +
          ((t : ℂ) • projectionPhaseNormal) * ((t : ℂ) • projectionPhaseNormal) := by
      noncomm_ring
    _ = projectionPhaseProjection + 0 + (t : ℂ) • projectionPhaseNormal + 0 := by
      rw [projectionPhaseProjection_sq, mul_smul_comm, projectionPhaseProjection_mul_normal,
        smul_zero, smul_mul_assoc, projectionPhaseNormal_mul_projection, smul_mul_assoc,
        mul_smul_comm, projectionPhaseNormal_sq, smul_zero]
    _ = projectionPhaseProjection + (t : ℂ) • projectionPhaseNormal := by simp

theorem projectionPhaseShearFamily_zero :
    projectionPhaseShearFamily 0 = projectionPhaseProjection := by
  simp [projectionPhaseShearFamily]

/-- The normal corner is the exact derivative of the idempotent shear at every real parameter. -/
theorem hasDerivAt_projectionPhaseShearFamily (t : ℝ) :
    HasDerivAt projectionPhaseShearFamily projectionPhaseNormal t := by
  unfold projectionPhaseShearFamily
  simpa using ((hasDerivAt_id (t : ℂ)).comp_ofReal.smul_const projectionPhaseNormal).const_add
    projectionPhaseProjection

/-- The Hodge--Dirac supercharge of the normal corner reconstructs the full Pauli-X tangent. -/
theorem brstHodgeDirac_projectionPhaseNormal_eq_X :
    HTGeometry.brstHodgeDiracOperator projectionPhaseNormal = projectionPhaseX := by
  exact brstHodgeDiracOperator_projectionNormalCorner_eq_tangent
    projectionPhaseProjection projectionPhaseX projectionPhaseProjection_sq
    projectionPhaseProjection_isSelfAdjoint.adjoint_eq
    projectionPhaseX_isSelfAdjoint.adjoint_eq projectionPhaseX_tangent_projection

/-- The Hodge Hamiltonian of the normal corner is the identity translation. -/
theorem brstHodgeHamiltonian_projectionPhaseNormal_eq_one :
    HTGeometry.brstHodgeHamiltonian projectionPhaseNormal = 1 := by
  calc
    HTGeometry.brstHodgeHamiltonian projectionPhaseNormal =
        HTGeometry.brstHodgeDiracOperator projectionPhaseNormal *
          HTGeometry.brstHodgeDiracOperator projectionPhaseNormal :=
      (HTGeometry.brstHodgeDiracOperator_sq_eq_hamiltonian projectionPhaseNormal
        projectionPhaseNormal_sq).symm
    _ = projectionPhaseX * projectionPhaseX := by
      rw [brstHodgeDirac_projectionPhaseNormal_eq_X]
    _ = 1 := projectionPhaseX_sq

/-- The normal corner and its adjoint give a closed chiral `D = 1`, `N = 2` realization. -/
def projectionPhaseChiralD1N2 : SuperPoincare.D1N2Chiral ProjectionPhaseEnd where
  supercharge := projectionPhaseNormal
  conjugateSupercharge := projectionPhaseNormal.adjoint
  momentum := 1
  supercharge_sq_zero := projectionPhaseNormal_sq
  conjugateSupercharge_sq_zero :=
    HTGeometry.adjoint_mul_self_eq_zero_of_self_mul_self_eq_zero projectionPhaseNormal
      projectionPhaseNormal_sq
  mixed_anticommutator := by
    simpa [HTGeometry.brstHodgeHamiltonian_eq_adjoint_mul_add_mul_adjoint, add_comm] using
      brstHodgeHamiltonian_projectionPhaseNormal_eq_one

/-- The existing first real supercharge is the Hodge--Dirac form of the chiral charge. -/
theorem projectionPhaseD1N2_supercharge0_eq_chiral_dirac :
    projectionPhaseD1N2.supercharge0 =
      HTGeometry.brstHodgeDiracOperator projectionPhaseChiralD1N2.supercharge := by
  exact brstHodgeDirac_projectionPhaseNormal_eq_X.symm

/-- The existing second real supercharge is the Hodge co-Dirac form of the chiral charge. -/
theorem projectionPhaseD1N2_supercharge1_eq_chiral_coDirac :
    projectionPhaseD1N2.supercharge1 =
      HTGeometry.brstHodgeCoDiracOperator projectionPhaseChiralD1N2.supercharge := by
  change projectionPhaseY = HTGeometry.brstHodgeCoDiracOperator projectionPhaseNormal
  unfold projectionPhaseY projectionPhaseNormal
  exact projectionPhaseRotation_eq_brstHodgeCoDiracOperator
    projectionPhaseProjection projectionPhaseX
    projectionPhaseProjection_isSelfAdjoint.adjoint_eq
    projectionPhaseX_isSelfAdjoint.adjoint_eq

end RHTower

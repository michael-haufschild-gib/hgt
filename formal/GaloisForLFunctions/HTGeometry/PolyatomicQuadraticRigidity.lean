import GaloisForLFunctions.HTGeometry.PolyatomicWeakCollision
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Classification of quadratic collision invariants

The conserved subspace of §4.2 of arXiv:2608.29825 can be audited directly on the
actual collision map, without assuming a nullspace description. A collision
with opposite incoming velocities and no outgoing translational energy detects
every quadratic form that is not the kinetic part of total energy.
Consequently the only tests quadratic in velocity and affine in internal
energy that vanish on every collision are the five conserved moments.
This classifies this polynomial class, not arbitrary measurable invariants or
the kernel of a particular integrated collision operator.
-/

open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The full quadratic-velocity, affine-internal-energy test class. -/
def polyatomicQuadraticTest (Q : QuadraticForm ℝ CollisionVelocity)
    (mass energy : ℝ) (momentum v : CollisionVelocity) (I : ℝ) : ℝ :=
  mass + inner ℝ momentum v + Q v + energy * I

/-- Opposite incoming velocities, all relative kinetic energy sent into one
internal channel. The direction is physically irrelevant at this endpoint. -/
def polyatomicThermalizingEvent (v : CollisionVelocity) (s : CollisionDirection) :
    PolyatomicCollisionEvent where
  v := v
  w := -v
  I := 0
  J := 0
  kinetic := ⟨0, by constructor <;> norm_num⟩
  internal := ⟨0, by constructor <;> norm_num⟩
  direction := s

/-- The available energy of opposite velocities is their common squared speed. -/
theorem polyatomicCollisionEnergy_opposite (v : CollisionVelocity) :
    polyatomicCollisionEnergy v (-v) 0 0 = ‖v‖^2 := by
  simp only [polyatomicCollisionEnergy, NNReal.coe_zero, add_zero, sub_neg_eq_add]
  rw [← two_smul ℝ v, norm_smul]
  norm_num
  ring

/-- One explicit family of physical collisions detects the entire anisotropic
quadratic defect. -/
theorem polyatomicQuadraticTest_thermalizing
    (Q : QuadraticForm ℝ CollisionVelocity) (mass energy : ℝ)
    (momentum v : CollisionVelocity) (s : CollisionDirection) :
    polyatomicTestDefect (polyatomicQuadraticTest Q mass energy momentum)
      (polyatomicThermalizingEvent v s) = energy * ‖v‖^2 - 2 * Q v := by
  simp [polyatomicTestDefect, polyatomicQuadraticTest, polyatomicThermalizingEvent,
    polyatomicVelocitiesOut, polyatomicRelativeOut, polyatomicInternalOut,
    polyatomicCollisionEnergy_opposite, Q.map_neg]
  ring

/-- Exact classification: conservation on every physical collision forces the
quadratic form to be the kinetic part of the same total-energy coefficient. -/
theorem polyatomicQuadraticTest_invariant_iff
    (Q : QuadraticForm ℝ CollisionVelocity) (mass energy : ℝ)
    (momentum : CollisionVelocity) (s : CollisionDirection) :
    (∀ event, polyatomicTestDefect (polyatomicQuadraticTest Q mass energy momentum) event = 0) ↔
      ∀ v, Q v = energy * (‖v‖^2 / 2) := by
  constructor
  · intro h v
    have hv := h (polyatomicThermalizingEvent v s)
    rw [polyatomicQuadraticTest_thermalizing] at hv
    linarith
  · intro h event
    have ht : polyatomicQuadraticTest Q mass energy momentum =
        polyatomicInvariantTest mass energy momentum := by
      funext v I
      dsimp [polyatomicQuadraticTest, polyatomicInvariantTest]
      rw [h v]
      ring
    rw [ht]
    exact polyatomicInvariantTest_defect mass energy momentum event

/-- The endpoint collision family already tests every invariant in this class. -/
theorem polyatomicQuadraticTest_endpoint_complete
    (Q : QuadraticForm ℝ CollisionVelocity) (mass energy : ℝ)
    (momentum : CollisionVelocity) (s : CollisionDirection) :
    (∀ v, polyatomicTestDefect (polyatomicQuadraticTest Q mass energy momentum)
      (polyatomicThermalizingEvent v s) = 0) ↔
    (∀ event, polyatomicTestDefect (polyatomicQuadraticTest Q mass energy momentum) event = 0) := by
  rw [polyatomicQuadraticTest_invariant_iff Q mass energy momentum s]
  simp_rw [polyatomicQuadraticTest_thermalizing]
  constructor <;> intro h v <;> have hv := h v <;> linarith

/-- Every non-energy quadratic form has an explicit physical collision witness. -/
theorem polyatomicQuadraticTest_violation_iff
    (Q : QuadraticForm ℝ CollisionVelocity) (mass energy : ℝ)
    (momentum : CollisionVelocity) (s : CollisionDirection) :
    (∃ event, polyatomicTestDefect (polyatomicQuadraticTest Q mass energy momentum) event ≠ 0) ↔
      ∃ v, Q v ≠ energy * (‖v‖^2 / 2) := by
  simpa only [not_forall] using
    not_congr (polyatomicQuadraticTest_invariant_iff Q mass energy momentum s)

end
end GaloisForLFunctions.HTGeometry

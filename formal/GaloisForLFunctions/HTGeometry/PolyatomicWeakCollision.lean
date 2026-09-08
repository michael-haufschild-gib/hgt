import GaloisForLFunctions.HTGeometry.PolyatomicKinematics
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Closed weak conservation laws for explicit polyatomic collisions

The Borgnakke--Larsen map from arXiv:2608.29825 conserves a five-parameter
space of test functions: mass, three momentum coordinates, and total
molecular energy. The symmetrized weak defect of every such test vanishes
pointwise. Therefore arbitrary weighted integrals and finite quadrature
measures conserve these moments without any residual integrability premise.
The five test parameters are independent. No claim is made that an arbitrary
collision kernel has no additional invariants.
-/

open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Physical event data; conservation is a theorem of its explicit map, not a field. -/
structure PolyatomicCollisionEvent where
  v : CollisionVelocity
  w : CollisionVelocity
  I : NNReal
  J : NNReal
  kinetic : CollisionPartition
  internal : CollisionPartition
  direction : CollisionDirection

/-- The five collision-invariant test coefficients, in coordinate-free momentum notation. -/
def polyatomicInvariantTest (mass energy : ℝ) (momentum : CollisionVelocity)
    (v : CollisionVelocity) (I : ℝ) : ℝ :=
  mass + inner ℝ momentum v + energy * (‖v‖ ^ 2 / 2 + I)

/-- Symmetrized outgoing-minus-incoming weak collision defect. -/
def polyatomicTestDefect (test : CollisionVelocity → ℝ → ℝ)
    (event : PolyatomicCollisionEvent) : ℝ :=
  let vout := polyatomicVelocitiesOut event.v event.w event.I event.J event.kinetic event.direction
  let Iout := polyatomicInternalOut event.v event.w event.I event.J event.kinetic event.internal
  test vout.1 Iout.1 + test vout.2 Iout.2 - test event.v event.I - test event.w event.J

/-- All five conserved moments have identically zero weak defect for every event. -/
theorem polyatomicInvariantTest_defect (mass energy : ℝ) (momentum : CollisionVelocity)
    (event : PolyatomicCollisionEvent) :
    polyatomicTestDefect (polyatomicInvariantTest mass energy momentum) event = 0 := by
  have hp := congrArg (fun v => inner ℝ momentum v)
    (polyatomicVelocitiesOut_momentum event.v event.w event.I event.J event.kinetic event.direction)
  simp only [inner_add_right] at hp
  have he := polyatomicLabEnergy_conserved event.v event.w event.I event.J
    event.kinetic event.internal event.direction
  dsimp only [polyatomicTestDefect, polyatomicInvariantTest]
  linear_combination hp + energy * he

/-- The mass, momentum, and energy coefficients really specify independent test functions. -/
theorem polyatomicInvariantTest_zero_iff (mass energy : ℝ) (momentum : CollisionVelocity) :
    (∀ (v : CollisionVelocity) (I : NNReal), polyatomicInvariantTest mass energy momentum v I = 0) ↔
      mass = 0 ∧ momentum = 0 ∧ energy = 0 := by
  constructor
  · intro h
    have hm := h 0 0
    simp only [polyatomicInvariantTest, inner_zero_right, norm_zero, zero_pow two_ne_zero,
      zero_div, NNReal.coe_zero, add_zero, mul_zero] at hm
    have he := h 0 1
    simp only [polyatomicInvariantTest, hm, inner_zero_right, norm_zero,
      zero_pow two_ne_zero, zero_div, NNReal.coe_one, zero_add, mul_one] at he
    have hp := h momentum 0
    simp only [polyatomicInvariantTest, hm, he, zero_mul, add_zero, zero_add] at hp
    have hnorm : ‖momentum‖ ^ 2 = 0 := by
      simpa only [real_inner_self_eq_norm_sq] using hp
    exact ⟨hm, norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm), he⟩
  · rintro ⟨rfl, rfl, rfl⟩ v I
    simp [polyatomicInvariantTest]

/-- An arbitrary weighted weak collision integral on an arbitrary event parameter space. -/
def polyatomicWeakCollision {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (events : Ω → PolyatomicCollisionEvent) (weight : Ω → ℝ)
    (test : CollisionVelocity → ℝ → ℝ) : ℝ :=
  ∫ z, weight z * polyatomicTestDefect test (events z) ∂μ

/-- Invariant integrands are integrable for every event measure and every weight. -/
theorem polyatomicWeakCollision_invariant_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (events : Ω → PolyatomicCollisionEvent) (weight : Ω → ℝ)
    (mass energy : ℝ) (momentum : CollisionVelocity) :
    Integrable (fun z => weight z *
      polyatomicTestDefect (polyatomicInvariantTest mass energy momentum) (events z)) μ := by
  simp only [polyatomicInvariantTest_defect, mul_zero]
  exact integrable_zero _ _ _

/-- The symmetrized weak operator annihilates the complete five-parameter invariant family. -/
theorem polyatomicWeakCollision_invariants {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (events : Ω → PolyatomicCollisionEvent) (weight : Ω → ℝ)
    (mass energy : ℝ) (momentum : CollisionVelocity) :
    polyatomicWeakCollision μ events weight (polyatomicInvariantTest mass energy momentum) = 0 := by
  simp only [polyatomicWeakCollision, polyatomicInvariantTest_defect, mul_zero, integral_zero]

/-- Multiplying by arbitrary scalar internal-state factors leaves the same invariant family. -/
theorem polyatomicWeakCollision_spectator_invariants {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (events : Ω → PolyatomicCollisionEvent) (weight spectator : Ω → ℝ)
    (mass energy : ℝ) (momentum : CollisionVelocity) :
    polyatomicWeakCollision μ events (fun z => weight z * spectator z)
      (polyatomicInvariantTest mass energy momentum) = 0 :=
  polyatomicWeakCollision_invariants μ events _ mass energy momentum

end GaloisForLFunctions.HTGeometry

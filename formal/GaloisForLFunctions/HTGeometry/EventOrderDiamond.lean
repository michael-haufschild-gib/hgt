import GaloisForLFunctions.HTGeometry.EventConnectionDescent
import Mathlib.Algebra.Lie.Classical

/-!
# Typed event-order diamond

A primitive event may change the type of the state and therefore the type of the next admissible
event. For two histories with common source and target,

`S --firstA--> A --thenB--> T`

and

`S --firstB--> B --thenA--> T`,

their typed order defect is the difference of the two composites. No event map is assumed
invertible.

This file proves:

* arbitrary changes of frame at the four vertices cancel at the intermediate vertices and leave
  endpoint covariance;
* vanishing of the defect is frame independent;
* common pre- and post-history compose with the defect;
* context-independent endomorphisms reduce the defect to a commutator, whose finite matrix trace
  vanishes; and
* every linear map occurs as a typed diamond defect.

The last theorem is a no-selection result. Typed diamonds provide a possible carrier for an order
effect, but without a separately derived event law they do not select curvature, gravity, a gauge
group, or physical dynamics.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R S A B T S' A' B' T' P Q : Type*}
variable [CommRing R]
variable [AddCommGroup S] [Module R S]
variable [AddCommGroup A] [Module R A]
variable [AddCommGroup B] [Module R B]
variable [AddCommGroup T] [Module R T]
variable [AddCommGroup S'] [Module R S']
variable [AddCommGroup A'] [Module R A']
variable [AddCommGroup B'] [Module R B']
variable [AddCommGroup T'] [Module R T']
variable [AddCommGroup P] [Module R P]
variable [AddCommGroup Q] [Module R Q]

/-- Difference between two complete two-step histories with common source and target. -/
def eventOrderDiamondDefect
    (firstA : S →ₗ[R] A) (thenB : A →ₗ[R] T)
    (firstB : S →ₗ[R] B) (thenA : B →ₗ[R] T) :
    S →ₗ[R] T :=
  thenB.comp firstA - thenA.comp firstB

/-- A typed diamond has zero defect exactly when its two complete histories agree. -/
theorem eventOrderDiamondDefect_eq_zero_iff
    (firstA : S →ₗ[R] A) (thenB : A →ₗ[R] T)
    (firstB : S →ₗ[R] B) (thenA : B →ₗ[R] T) :
    eventOrderDiamondDefect firstA thenB firstB thenA = 0 ↔
      thenB.comp firstA = thenA.comp firstB := by
  unfold eventOrderDiamondDefect
  exact sub_eq_zero

/-- Change the source and target frames of a linear event map. -/
def eventGaugeTransform
    (sourceGauge : S ≃ₗ[R] S') (targetGauge : T ≃ₗ[R] T')
    (f : S →ₗ[R] T) : S' →ₗ[R] T' :=
  targetGauge.toLinearMap.comp (f.comp sourceGauge.symm.toLinearMap)

/-- Evaluation form of an event-frame change. -/
@[simp]
theorem eventGaugeTransform_apply
    (sourceGauge : S ≃ₗ[R] S') (targetGauge : T ≃ₗ[R] T')
    (f : S →ₗ[R] T) (x : S) :
    eventGaugeTransform sourceGauge targetGauge f (sourceGauge x) =
      targetGauge (f x) := by
  simp [eventGaugeTransform, LinearMap.comp_apply]

/--
Frame changes respect composition. The frame at the intermediate event state cancels exactly.
-/
theorem eventGaugeTransform_comp
    (sourceGauge : S ≃ₗ[R] S') (middleGauge : A ≃ₗ[R] A')
    (targetGauge : T ≃ₗ[R] T')
    (f : S →ₗ[R] A) (g : A →ₗ[R] T) :
    eventGaugeTransform sourceGauge targetGauge (g.comp f) =
      (eventGaugeTransform middleGauge targetGauge g).comp
        (eventGaugeTransform sourceGauge middleGauge f) := by
  ext x
  obtain ⟨y, rfl⟩ := sourceGauge.surjective x
  simp

/--
**Typed-diamond gauge covariance.** The two intermediate frame changes cancel, so the complete
order defect transforms only at its common source and target.
-/
theorem eventOrderDiamondDefect_gauge_covariant
    (sourceGauge : S ≃ₗ[R] S') (aGauge : A ≃ₗ[R] A')
    (bGauge : B ≃ₗ[R] B') (targetGauge : T ≃ₗ[R] T')
    (firstA : S →ₗ[R] A) (thenB : A →ₗ[R] T)
    (firstB : S →ₗ[R] B) (thenA : B →ₗ[R] T) :
    eventOrderDiamondDefect
        (eventGaugeTransform sourceGauge aGauge firstA)
        (eventGaugeTransform aGauge targetGauge thenB)
        (eventGaugeTransform sourceGauge bGauge firstB)
        (eventGaugeTransform bGauge targetGauge thenA) =
      eventGaugeTransform sourceGauge targetGauge
        (eventOrderDiamondDefect firstA thenB firstB thenA) := by
  rw [eventOrderDiamondDefect]
  rw [← eventGaugeTransform_comp sourceGauge aGauge targetGauge firstA thenB]
  rw [← eventGaugeTransform_comp sourceGauge bGauge targetGauge firstB thenA]
  ext x
  simp [eventGaugeTransform, eventOrderDiamondDefect, LinearMap.comp_apply]

/-- An invertible endpoint-frame change preserves and reflects vanishing. -/
theorem eventGaugeTransform_eq_zero_iff
    (sourceGauge : S ≃ₗ[R] S') (targetGauge : T ≃ₗ[R] T')
    (f : S →ₗ[R] T) :
    eventGaugeTransform sourceGauge targetGauge f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext x
    apply targetGauge.injective
    simpa using LinearMap.congr_fun h (sourceGauge x)
  · rintro rfl
    simp [eventGaugeTransform]

/-- Vanishing of the typed event-order defect is independent of every vertex frame. -/
theorem eventOrderDiamondDefect_gauge_eq_zero_iff
    (sourceGauge : S ≃ₗ[R] S') (aGauge : A ≃ₗ[R] A')
    (bGauge : B ≃ₗ[R] B') (targetGauge : T ≃ₗ[R] T')
    (firstA : S →ₗ[R] A) (thenB : A →ₗ[R] T)
    (firstB : S →ₗ[R] B) (thenA : B →ₗ[R] T) :
    eventOrderDiamondDefect
        (eventGaugeTransform sourceGauge aGauge firstA)
        (eventGaugeTransform aGauge targetGauge thenB)
        (eventGaugeTransform sourceGauge bGauge firstB)
        (eventGaugeTransform bGauge targetGauge thenA) = 0 ↔
      eventOrderDiamondDefect firstA thenB firstB thenA = 0 := by
  rw [eventOrderDiamondDefect_gauge_covariant]
  exact eventGaugeTransform_eq_zero_iff sourceGauge targetGauge _

/-- Attaching the same later history postcomposes the order defect. -/
theorem eventOrderDiamondDefect_postcompose
    (firstA : S →ₗ[R] A) (thenB : A →ₗ[R] T)
    (firstB : S →ₗ[R] B) (thenA : B →ₗ[R] T)
    (post : T →ₗ[R] Q) :
    eventOrderDiamondDefect firstA (post.comp thenB) firstB (post.comp thenA) =
      post.comp (eventOrderDiamondDefect firstA thenB firstB thenA) := by
  ext x
  simp [eventOrderDiamondDefect, LinearMap.comp_apply]

/-- Attaching the same earlier history precomposes the order defect. -/
theorem eventOrderDiamondDefect_precompose
    (pre : P →ₗ[R] S)
    (firstA : S →ₗ[R] A) (thenB : A →ₗ[R] T)
    (firstB : S →ₗ[R] B) (thenA : B →ₗ[R] T) :
    eventOrderDiamondDefect (firstA.comp pre) thenB (firstB.comp pre) thenA =
      (eventOrderDiamondDefect firstA thenB firstB thenA).comp pre := by
  ext x
  simp [eventOrderDiamondDefect, LinearMap.comp_apply]

/--
If event types and event maps ignore prior history, the typed diamond collapses to an ordinary
endomorphism commutator.
-/
theorem eventOrderDiamondDefect_contextIndependent
    (firstA firstB : Module.End R S) :
    eventOrderDiamondDefect firstA firstB firstB firstA =
      endCommutator firstB firstA := by
  rfl

/--
The context-independent finite-matrix order defect has zero trace. This is the exact central
channel obstruction for a plain finite commutator.
-/
theorem matrix_contextIndependent_orderDefect_trace_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (firstA firstB : Matrix n n R) :
    Matrix.trace (firstB * firstA - firstA * firstB) = 0 := by
  simpa only [LieRing.of_associative_ring_bracket] using
    LieAlgebra.matrix_trace_commutator_zero n R firstB firstA

/--
**No-selection theorem.** Every linear map is a typed event-order defect. Therefore the diamond
carrier alone imposes no curvature, gauge-group, or dynamical selection.
-/
theorem eventOrderDiamondDefect_universal
    (D : S →ₗ[R] T) :
    eventOrderDiamondDefect (LinearMap.id) D (0 : Module.End R S) (0 : S →ₗ[R] T) =
      D := by
  ext x
  simp [eventOrderDiamondDefect]

/-! ## Fixed-carrier block dilation -/

/-- One fixed carrier containing all four vertices of a typed event diamond. -/
abbrev EventDiamondFixedCarrier :=
  S × (A × (B × T))

/-- Embed the typed diamond's source into the source block of its fixed carrier. -/
def eventDiamondSourceInclusion :
    S →ₗ[R] EventDiamondFixedCarrier (S := S) (A := A) (B := B) (T := T) where
  toFun s := (s, (0, (0, 0)))
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Read the typed diamond's target block from its fixed carrier. -/
def eventDiamondTargetProjection :
    EventDiamondFixedCarrier (S := S) (A := A) (B := B) (T := T) →ₗ[R] T where
  toFun x := x.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Lift the first event on the upper path to a block endomorphism. -/
def eventDiamondFirstALift
    (firstA : S →ₗ[R] A) :
    Module.End R (EventDiamondFixedCarrier (S := S) (A := A) (B := B) (T := T)) where
  toFun x := (0, (firstA x.1, (0, 0)))
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Lift the second event on the upper path to a block endomorphism. -/
def eventDiamondThenBLift
    (thenB : A →ₗ[R] T) :
    Module.End R (EventDiamondFixedCarrier (S := S) (A := A) (B := B) (T := T)) where
  toFun x := (0, (0, (0, thenB x.2.1)))
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Lift the first event on the lower path to a block endomorphism. -/
def eventDiamondFirstBLift
    (firstB : S →ₗ[R] B) :
    Module.End R (EventDiamondFixedCarrier (S := S) (A := A) (B := B) (T := T)) where
  toFun x := (0, (0, (firstB x.1, 0)))
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Lift the second event on the lower path to a block endomorphism. -/
def eventDiamondThenALift
    (thenA : B →ₗ[R] T) :
    Module.End R (EventDiamondFixedCarrier (S := S) (A := A) (B := B) (T := T)) where
  toFun x := (0, (0, (0, thenA x.2.2.1)))
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- The fixed-carrier upper path exactly reconstructs the original typed upper path. -/
theorem eventDiamondFixedCarrier_upper_reconstruct
    (firstA : S →ₗ[R] A) (thenB : A →ₗ[R] T) :
    (eventDiamondTargetProjection (R := R) (S := S) (A := A) (B := B) (T := T)).comp
        (((eventDiamondThenBLift (R := R) (S := S) (B := B) thenB).comp
          (((eventDiamondFirstALift (R := R) (B := B) (T := T) firstA).comp
            (eventDiamondSourceInclusion
              (R := R) (S := S) (A := A) (B := B) (T := T)))))) =
      thenB.comp firstA := by
  ext x
  rfl

/-- The fixed-carrier lower path exactly reconstructs the original typed lower path. -/
theorem eventDiamondFixedCarrier_lower_reconstruct
    (firstB : S →ₗ[R] B) (thenA : B →ₗ[R] T) :
    (eventDiamondTargetProjection (R := R) (S := S) (A := A) (B := B) (T := T)).comp
        (((eventDiamondThenALift (R := R) (S := S) (A := A) thenA).comp
          (((eventDiamondFirstBLift (R := R) (A := A) (T := T) firstB).comp
            (eventDiamondSourceInclusion
              (R := R) (S := S) (A := A) (B := B) (T := T)))))) =
      thenA.comp firstB := by
  ext x
  rfl

/--
**Fixed-carrier dilation no-go.** Every typed event diamond and its complete order defect are
exactly reproduced by four block endomorphisms of one larger fixed carrier.
-/
theorem eventDiamondFixedCarrier_defect_reconstruct
    (firstA : S →ₗ[R] A) (thenB : A →ₗ[R] T)
    (firstB : S →ₗ[R] B) (thenA : B →ₗ[R] T) :
    (eventDiamondTargetProjection (R := R) (S := S) (A := A) (B := B) (T := T)).comp
        ((eventOrderDiamondDefect
          (eventDiamondFirstALift (R := R) (B := B) (T := T) firstA)
          (eventDiamondThenBLift (R := R) (S := S) (B := B) thenB)
          (eventDiamondFirstBLift (R := R) (A := A) (T := T) firstB)
          (eventDiamondThenALift (R := R) (S := S) (A := A) thenA)).comp
            (eventDiamondSourceInclusion
              (R := R) (S := S) (A := A) (B := B) (T := T))) =
      eventOrderDiamondDefect firstA thenB firstB thenA := by
  ext x
  rfl

end

end GaloisForLFunctions.HTGeometry

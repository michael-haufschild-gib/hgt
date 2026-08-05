import GaloisForLFunctions.HTGeometry.PointedTransportFirstLossLaw

/-!
# Conservative transports on a pointed range exist

A transport is conservative on a delivered pointed range when it annihilates none of the delivered
values except the zero one.  Every injective zero-preserving transport is conservative on every
range, the identity is one, and the zero source is delivered conservatively by every transport — so
the first-loss law has instances on both sides of its serial composition.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **An injective zero-preserving transport is conservative on every pointed range.** -/
theorem conservativeOnPointedRange_of_injective {V W P : Type*} [Zero V] [Zero W]
    {T : V → W} (hT0 : T 0 = 0) (hinj : Function.Injective T) (x : P → V) :
    ConservativeOnPointedRange T x := by
  intro p hp
  exact hinj (by rw [hp, hT0])

/-- The identity transport is conservative on every pointed range. -/
theorem conservativeOnPointedRange_id {V P : Type*} [Zero V] (x : P → V) :
    ConservativeOnPointedRange (id : V → V) x :=
  conservativeOnPointedRange_of_injective rfl Function.injective_id x

/-- The zero source is conservatively delivered by every transport. -/
theorem conservativeOnPointedRange_zero_source {V W P : Type*} [Zero V] [Zero W]
    (T : V → W) : ConservativeOnPointedRange T (fun _ : P => (0 : V)) := by
  intro _ _
  rfl

end GaloisForLFunctions.HTGeometry

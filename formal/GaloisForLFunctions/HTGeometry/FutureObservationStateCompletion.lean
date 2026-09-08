import GaloisForLFunctions.HTGeometry.FiniteEventTimingRecovery
import GaloisForLFunctions.HTGeometry.SourceTestPartitionUniversality
import Mathlib.Logic.Function.Iterate

/-!
# The minimal closed state retaining all future observations

Gebbie, arXiv:2608.22497v2, Proposition 3, distinguishes a complete event state
from a projection that forgets its clock. The positive replacement is canonical:
identify states exactly when their complete future observation sequences agree.
The resulting quotient has a proved dynamics and is the coarsest dynamically
stable observation-preserving identification. It connects directly to the
corpus's exact source-test presentations. No closure assumption is imposed.
-/

namespace GaloisForLFunctions.HTGeometry
variable {X Y : Type*}

/-- Equality of all future readings, including the present reading. -/
def futureObservationSetoid (step : X → X) (obs : X → Y) : Setoid X where
  r x y := ∀ n : ℕ, obs (step^[n] x) = obs (step^[n] y)
  iseqv := ⟨fun _ _ => rfl, fun h n => (h n).symm, fun h₁ h₂ n => (h₁ n).trans (h₂ n)⟩

/-- Future-equivalent states remain equivalent after an actual step. -/
theorem futureObservationSetoid_step (step : X → X) (obs : X → Y) :
    ∀ x y, (futureObservationSetoid step obs) x y →
      (futureObservationSetoid step obs) (step x) (step y) := by
  intro x y h n
  simpa only [Function.iterate_succ_apply] using h (n + 1)

/-- Present observations descend because time zero is part of the future trace. -/
def futureObservationRead (step : X → X) (obs : X → Y) :
    Quotient (futureObservationSetoid step obs) → Y :=
  Quotient.lift obs (fun _ _ h => h 0)

/-- The quotient dynamics is constructed, not postulated. -/
def futureObservationStep (step : X → X) (obs : X → Y) :
    Quotient (futureObservationSetoid step obs) → Quotient (futureObservationSetoid step obs) :=
  Quotient.map step (futureObservationSetoid_step step obs)

/-- Every number of quotient steps agrees with the corresponding original dynamics. -/
theorem futureObservationStep_iterate (step : X → X) (obs : X → Y) (x : X) (n : ℕ) :
    (futureObservationStep step obs)^[n] (Quotient.mk _ x) =
      Quotient.mk _ (step^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rfl

/-- The completed state reproduces every future reading exactly. -/
theorem futureObservationRead_iterate (step : X → X) (obs : X → Y) (x : X) (n : ℕ) :
    futureObservationRead step obs ((futureObservationStep step obs)^[n] (Quotient.mk _ x)) =
      obs (step^[n] x) := by
  rw [futureObservationStep_iterate]
  rfl

/-- No two completed states can have the same complete future observation sequence. -/
theorem futureObservationTrace_injective (step : X → X) (obs : X → Y) :
    Function.Injective (fun q : Quotient (futureObservationSetoid step obs) =>
      fun n : ℕ => futureObservationRead step obs ((futureObservationStep step obs)^[n] q)) := by
  intro q r h
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      intro n
      have hn := congrFun h n
      simpa only [futureObservationRead_iterate] using hn

/-- Exact maximality among observation-preserving, dynamically stable identifications. -/
theorem futureObservationSetoid_isGreatest (step : X → X) (obs : X → Y) :
    IsGreatest {s : Setoid X |
      (∀ x y, s x y → obs x = obs y) ∧
      (∀ x y, s x y → s (step x) (step y))} (futureObservationSetoid step obs) := by
  constructor
  · exact ⟨fun _ _ h => h 0, futureObservationSetoid_step step obs⟩
  · intro s hs x y hxy n
    apply hs.1
    induction n with
    | zero => exact hxy
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hs.2 _ _ ih

/-- The existing source-test recognizer identifies exactly the same completed states. -/
theorem futureObservation_sourceTest_exact (step : X → X) (obs : X → Y) (x y : X) :
    (SourceTestPresentation.quotientRecognizer (futureObservationSetoid step obs)).ObservationallyEquivalent x y ↔
        ∀ n : ℕ, obs (step^[n] x) = obs (step^[n] y) :=
  SourceTestPresentation.quotientRecognizer_observationallyEquivalent_iff _ _ _

/-- Two consecutive readings already recover the full delayed binary state and clock. -/
theorem delayedBinaryEventStep_twoReadings_injective :
    Function.Injective (fun s : Bool × Bool => (s.1, (delayedBinaryEventStep s).1)) := by
  intro x y h
  rcases x with ⟨x, a⟩
  rcases y with ⟨y, b⟩
  cases x <;> cases a <;> cases y <;> cases b <;>
    simp_all [delayedBinaryEventStep]

/-- No hidden-clock state can be discarded by a lossless dynamically closed description. -/
theorem delayedBinaryEventStep_future_iff (x y : Bool × Bool) :
    (futureObservationSetoid delayedBinaryEventStep Prod.fst) x y ↔ x = y := by
  constructor
  · intro h
    apply delayedBinaryEventStep_twoReadings_injective
    exact Prod.ext (h 0) (h 1)
  · intro h
    subst y
    exact fun _ => rfl

end GaloisForLFunctions.HTGeometry

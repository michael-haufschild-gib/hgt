import GaloisForLFunctions.HTGeometry.ConstitutivePolarityRevision

/-!
# Arbitrary transition dynamics from endogenous compatibility

A state-indexed compatibility relation with one test can realize any prescribed transition
relation as an exact polar.  State dependence alone therefore imposes no dynamical law.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {S : Type u}

/-- Compatibility that stores the prescribed successor relation at the current state. -/
def constitutiveEndogenousCompatibility (next : S → Set S) (state candidate : S)
    (_ : PUnit) : Prop :=
  candidate ∈ next state

/-- One universal test recovers an arbitrary prescribed successor set exactly. -/
theorem constitutiveEndogenousCompatibility_realizes (next : S → Set S) (state : S) :
    constitutiveTestPolar
        (constitutiveEndogenousCompatibility next state) Set.univ =
      next state := by
  ext candidate
  simp [constitutiveTestPolar, constitutiveEndogenousCompatibility]

/-- The successor relation associated with a deterministic state update. -/
def constitutiveDeterministicTransition (update : S → S) (state : S) : Set S :=
  {update state}

/-- Every deterministic update is the one-test polar of an endogenous compatibility law. -/
theorem constitutiveEndogenousCompatibility_realizes_deterministic
    (update : S → S) (state : S) :
    constitutiveTestPolar
        (constitutiveEndogenousCompatibility
          (constitutiveDeterministicTransition update) state) Set.univ =
      {update state} := by
  exact constitutiveEndogenousCompatibility_realizes
    (constitutiveDeterministicTransition update) state

/-- **Conjugacy naturality.**  Relabelling the state space transports the endogenous compatibility
law and its one-test polar, so equivariance under renaming does not constrain the realized
dynamics. -/
theorem constitutiveEndogenousCompatibility_conjugate {S' : Type u}
    (e : S ≃ S') (next : S → Set S) (next' : S' → Set S')
    (hnat : ∀ s, next' (e s) = e '' next s) (state : S) :
    constitutiveTestPolar
        (constitutiveEndogenousCompatibility next' (e state)) Set.univ =
      e '' (constitutiveTestPolar
        (constitutiveEndogenousCompatibility next state) Set.univ) := by
  rw [constitutiveEndogenousCompatibility_realizes,
    constitutiveEndogenousCompatibility_realizes, hnat]

/-- Closed capstone: a one-test endogenous polarity realizes every transition system. -/
theorem constitutiveEndogenousCompatibilityUniversality_closed :
    ∀ (S : Type u) (next : S → Set S) (state : S),
      constitutiveTestPolar
          (constitutiveEndogenousCompatibility next state) Set.univ =
        next state := by
  intro S next state
  exact constitutiveEndogenousCompatibility_realizes next state

end GaloisForLFunctions.HTGeometry

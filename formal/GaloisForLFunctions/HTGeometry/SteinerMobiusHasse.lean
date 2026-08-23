import GaloisForLFunctions.HTGeometry.SteinerMobiusDuality

/-!
# Hasse reconstruction for Steiner--Möbius local functions

Anchored and Boolean functions declared local on a finite support packet are determined completely
by their restriction to subconfigurations of that packet.  Each local function space is therefore
linearly equivalent to the finite restriction profiles that actually occur.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Anchored-local functions are linearly equivalent to their realized finite support profiles. -/
noncomputable def anchoredLocalHasseEquivRealizedProfiles
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V) :
    anchoredLocalSubmodule (A := A) (base := base) (R := R) support ≃ₗ[R]
      LinearMap.range (anchoredLocalRestriction
        (A := A) (base := base) (R := R) support) :=
  LinearEquiv.ofInjective _ (anchoredLocalRestriction_injective support)

/-- Two anchored-local functions agree globally exactly when they agree on every configuration
supported in the declared packet. -/
theorem anchoredLocal_congr_hasse_iff
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V)
    (f g : anchoredLocalSubmodule (A := A) (base := base) (R := R) support) :
    (∀ i : {index : AnchoredConfiguration V A base //
        anchoredSupport index ⊆ support}, f.1 i.1 = g.1 i.1) ↔ f = g := by
  constructor
  · intro h
    apply anchoredLocalRestriction_injective support
    funext i
    exact h i
  · rintro rfl i
    rfl

/-- Boolean-local functions are linearly equivalent to their realized finite support profiles. -/
noncomputable def booleanLocalHasseEquivRealizedProfiles
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V) :
    booleanLocalSubmodule (R := R) support ≃ₗ[R]
      LinearMap.range (booleanLocalRestriction (R := R) support) :=
  LinearEquiv.ofInjective _ (booleanLocalRestriction_injective support)

/-- Two Boolean-local functions agree globally exactly when they agree on every subconfiguration
of the declared support packet. -/
theorem booleanLocal_congr_hasse_iff
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V)
    (f g : booleanLocalSubmodule (R := R) support) :
    (∀ i : {sites : Finset V // sites ⊆ support}, f.1 i.1 = g.1 i.1) ↔ f = g := by
  constructor
  · intro h
    apply booleanLocalRestriction_injective support
    funext i
    exact h i
  · rintro rfl i
    rfl

end

end GaloisForLFunctions.HTGeometry

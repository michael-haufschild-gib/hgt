import GaloisForLFunctions.HTGeometry.ABHN.Places
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces

/-!
# Exact-sequence contract for Albert--Brauer--Hasse--Noether

This file fixes the literal end contract of the formalization.  It is a specification, not an
axiom: an inhabitant can exist only after Lean has constructed a global-to-local map and the sum
of local invariant maps, then proved injectivity, exactness, and surjectivity.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- The additive target `ℚ / ℤ` of the ABHN invariant sequence. -/
abbrev RatModInt := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- The exactness data for an ABHN sequence, stated without assuming an additive API on its
currently-quotient-defined Brauer carriers. -/
structure ABHNExactness (G L : Type*) (globalToLocal : G → L)
    (localInvariant : L → RatModInt) : Prop where
  globalToLocal_injective : Function.Injective globalToLocal
  exact_globalToLocal_localInvariant : Function.Exact globalToLocal localInvariant
  localInvariant_surjective : Function.Surjective localInvariant

/-- The precise remaining contract for a number field. -/
def NumberFieldABHNExactness (K : Type*) [Field K] [NumberField K]
    (globalToLocal : BrauerGroup K → RestrictedLocalBrauerClasses K)
    (localInvariant : RestrictedLocalBrauerClasses K → RatModInt) : Prop :=
  ABHNExactness _ _ globalToLocal localInvariant

/-- The precise remaining contract for the rational global function field `F(t)`. -/
def RationalFunctionABHNExactness (F : Type*) [Field F] [Finite F]
    (globalToLocal : BrauerGroup (RatFunc F) → RationalFunctionRestrictedLocalBrauerClasses F)
    (localInvariant : RationalFunctionRestrictedLocalBrauerClasses F → RatModInt) : Prop :=
  ABHNExactness _ _ globalToLocal localInvariant

end GaloisForLFunctions.HTGeometry.ABHN

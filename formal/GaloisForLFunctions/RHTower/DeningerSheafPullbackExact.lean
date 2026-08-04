import GaloisForLFunctions.RHTower.DeningerLogKummerSequence
import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Inverse image of abelian sheaves is exact

The inverse image functor on sheaves of abelian groups along a continuous map preserves finite
limits, because the inverse image of open sets is a flat functor, and it preserves colimits because
it is a left adjoint.  So it carries short exact sequences to short exact sequences, and the Kummer
sequence of the divisorial log structure pulls back to a short exact sequence on any space over the
arithmetic curve.

* `deningerSheafPullback_preservesFiniteLimits` : left exactness of the inverse image.
* `deningerSheafPullback_shortExact` : the inverse image of a short exact sequence.
* `deningerPulledBackKummerComplex_shortExact` : the pulled back Kummer sequence.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopCat

set_option maxHeartbeats 1000000 in
attribute [local instance] CategoryTheory.Limits.reflectsLimits_of_reflectsIsomorphisms in
/-- **The inverse image of abelian sheaves is left exact.** -/
theorem deningerSheafPullback_preservesFiniteLimits {X Y : TopCat.{0}} (f : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := by
  unfold TopCat.Sheaf.pullback
  apply CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits

/-- **The inverse image of abelian sheaves is exact**: it carries a short exact sequence to a short
exact sequence. -/
theorem deningerSheafPullback_shortExact {X Y : TopCat.{0}} (f : X ⟶ Y)
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} Y)) (hS : S.ShortExact) :
    (S.map (TopCat.Sheaf.pullback AddCommGrpCat.{0} f)).ShortExact := by
  haveI := deningerSheafPullback_preservesFiniteLimits f
  exact hS.map_of_exact _

/-- The Kummer sequence of the divisorial log structure, pulled back along a map to the arithmetic
curve. -/
noncomputable def deningerPulledBackKummerComplex {X : TopCat.{0}} (a : X ⟶ deningerArithBase)
    (P : Finset Nat.Primes) : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  (deningerLogKummerComplex P).map (TopCat.Sheaf.pullback AddCommGrpCat.{0} a)

/-- **The pulled back Kummer sequence is short exact.** -/
theorem deningerPulledBackKummerComplex_shortExact {X : TopCat.{0}}
    (a : X ⟶ deningerArithBase) (P : Finset Nat.Primes) :
    (deningerPulledBackKummerComplex a P).ShortExact :=
  deningerSheafPullback_shortExact a _ (deningerLogKummerComplex_shortExact P)

end RHTower

import GaloisForLFunctions.RHTower.Deninger.DeningerDerivedToposComparison
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# The derived-topos comparison at the quotient stack of a point

The abstract derived-topos comparison of `DeningerDerivedToposComparison.lean` is instantiated here
at the smallest genuine quotient stack, `c : [pt/G] → pt`.  Sheaves on `[pt/G]` are
`G`-representations, sheaves on the coarse quotient are modules, and Deninger's degreewise
invariant coefficient `c_* = (π_* −)^G` is the invariants functor.  Nothing in this file is a
weakening: it exists so that the hypotheses of the abstract theorem are exhibited as satisfied by
an actual quotient stack rather than assumed.

Three facts are proved, and none of them was in mathlib:

* `G`-representations have enough injective objects, transported along the equivalence with
  modules over the monoid algebra;
* the trivial-representation functor preserves finite limits, because it is right adjoint to
  coinvariants;
* hence the invariants functor preserves injective objects, which is the hypothesis Grothendieck's
  composition law needs, and it holds here without assumption.

* `RHTower.deningerRepEnoughInjectives` : `Rep k G` has enough injectives.
* `RHTower.deningerTrivialFunctor_preservesFiniteLimits` : the trivial representation is exact.
* `RHTower.deningerInvariants_preservesInjectiveObjects` : `(−)^G` preserves injectives.
* `RHTower.deningerRepHasDerivedCategory` : the derived category of `Rep k G` exists.
* `RHTower.deningerPointStackDerivedDescentIso` : derived descent along `[pt/G] → pt`.
* `RHTower.deningerPointStackComparisonIso` : equation `(3)` for `[pt/G] → pt`.
-/

open CategoryTheory Limits

namespace RHTower

universe u

section PointStack

variable (k G : Type u) [CommRing k] [Group G]

/-- **`G`-representations have enough injective objects.**  They are equivalent to modules over the
monoid algebra, and a module category over a ring in the same universe has enough injectives. -/
noncomputable instance deningerRepEnoughInjectives : EnoughInjectives (Rep.{u} k G) :=
  EnoughInjectives.of_equivalence
    (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G) :
      Rep.{u} k G ≌ ModuleCat.{u} (MonoidAlgebra k G)).functor

/-- **The trivial-representation functor is exact.**  It is right adjoint to the coinvariants
functor, so it preserves all limits, in particular the finite ones.  This is the pullback `c^*`
along `c : [pt/G] → pt`. -/
noncomputable instance deningerTrivialFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (Rep.trivialFunctor k G) := by
  have := (Rep.coinvariantsAdjunction k G).rightAdjoint_preservesLimits
  infer_instance

/-- **The invariants functor preserves injective objects.**  It is right adjoint to the exact
trivial-representation functor, so this is the special case of
`deningerCoarsePushforward_preservesInjectives` at `c : [pt/G] → pt`, and it is unconditional. -/
instance deningerInvariants_preservesInjectiveObjects :
    (Rep.invariantsFunctor k G).PreservesInjectiveObjects :=
  deningerCoarsePushforward_preservesInjectives (Rep.invariantsAdjunction k G)

/-- The derived category of `G`-representations exists; this witnesses that the
`HasDerivedCategory` hypotheses used below are satisfiable rather than vacuous. -/
theorem deningerRepHasDerivedCategory :
    Nonempty (HasDerivedCategory.{u + 1} (Rep.{u} k G)) :=
  ⟨HasDerivedCategory.standard _⟩

/-- The derived category of `k`-modules exists. -/
theorem deningerModuleHasDerivedCategory :
    Nonempty (HasDerivedCategory.{u + 1} (ModuleCat.{u} k)) :=
  ⟨HasDerivedCategory.standard _⟩

variable {k G}
variable [HasDerivedCategory.{u + 1} (Rep.{u} k G)]
  [HasDerivedCategory.{u + 1} (ModuleCat.{u} k)]

/-- **Derived descent along `c : [pt/G] → pt`.**  The derived global sections of the quotient stack
of a point are the derived invariants, and they are computed by the derived pushforward followed by
the coarse global sections.  This is `deningerDerivedDescentIso` at an honest quotient stack. -/
noncomputable def deningerPointStackDerivedDescentIso :
    (deningerStackGlobalSections (Rep.invariantsFunctor k G)
        (𝟭 (ModuleCat.{u} k))).rightDerivedFunctorPlus ≅
      (Rep.invariantsFunctor k G).rightDerivedFunctorPlus ⋙
        (𝟭 (ModuleCat.{u} k)).rightDerivedFunctorPlus :=
  deningerDerivedDescentIso (Rep.invariantsFunctor k G) (𝟭 (ModuleCat.{u} k))

/-- **Equation `(3)` at `c : [pt/G] → pt`.**  If the canonical comparison from the underived
invariant coefficient to the derived pushforward is a quasi-isomorphism at `Ã`, then the coarse
derived global sections of the invariant coefficient agree with the derived global sections of the
quotient stack. -/
noncomputable def deningerPointStackComparisonIso (Atilde : HomotopyCategory.Plus (Rep.{u} k G))
    (hcomp : IsIso (deningerCoarseComparison (Rep.invariantsFunctor k G) Atilde)) :
    (𝟭 (ModuleCat.{u} k)).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj
          ((Rep.invariantsFunctor k G).mapHomotopyCategoryPlus.obj Atilde)) ≅
      (deningerStackGlobalSections (Rep.invariantsFunctor k G)
          (𝟭 (ModuleCat.{u} k))).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj Atilde) :=
  deningerDerivedToposComparisonIso (Rep.invariantsFunctor k G) (𝟭 (ModuleCat.{u} k)) Atilde hcomp

end PointStack

end RHTower

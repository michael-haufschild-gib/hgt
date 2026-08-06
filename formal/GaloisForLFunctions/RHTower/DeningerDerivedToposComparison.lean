import GaloisForLFunctions.HTGeometry.DerivedFunctorPlusComposition
import GaloisForLFunctions.RHTower.DeningerCoarseStackScalarNoGo

/-!
# The derived-topos comparison for the coarse quotient

Let `c : [X̃/G] → X = X̃/G` be the map from Deninger's quotient stack to its coarse quotient and
let `Ã` be a `G`-equivariant coefficient complex.  Deninger's degreewise invariant coefficient is
the underived pushforward `A_X = c_* Ã = (π_* Ã)^G`, and there is a canonical comparison
`c_* Ã ⟶ R c_* Ã`.

This module supplies the derived-topos step that the card
`deninger-coarse-stack-exactness-spectrum-no-go` leaves open: applying `RΓ(X, −)` to that
comparison and invoking derived descent for the quotient stack gives

`RΓ(X, c_* Ã) ≃ RΓ([X̃/G], Ã)`.

Two facts do the work.

* Derived descent for the quotient stack is the statement that global sections on the stack are
  the invariant global sections on the coarse space, `Γ_{[X̃/G]} = Γ_X ∘ c_*`, *derived*.  The
  underived identity is Deninger's definition of the invariant coefficient, and the derived
  identity is Grothendieck's composition law `R(Γ_X ∘ c_*) ≅ RΓ_X ∘ Rc_*`, which is available
  because `c_*` preserves injective objects.  That preservation is not an assumption: `c_*` is
  right adjoint to the exact pullback `c^*`, and a right adjoint of a monomorphism-preserving
  functor preserves injectives.
* Hypothesis 1 of the card says the canonical comparison is a quasi-isomorphism.  In the bounded
  below derived category the canonical comparison *is* the unit of the right derived functor of
  `c_*`, so the hypothesis is literally the invertibility of that unit at `Ã`.

* `RHTower.deningerCoarsePushforward_preservesInjectives` : an exact left adjoint makes `c_*`
  preserve injectives.
* `RHTower.deningerCoarseComparison` : the canonical comparison `(2)`, `c_* Ã ⟶ R c_* Ã`.
* `RHTower.deningerStackGlobalSections` : `Γ_{[X̃/G]} = Γ_X ∘ c_*`, the definition `(1)` of the
  invariant coefficient read on global sections.
* `RHTower.deningerDerivedDescentIso` : derived descent, `R Γ_{[X̃/G]} ≅ RΓ_X ∘ Rc_*`.
* `RHTower.deningerDerivedToposComparisonIso` : equation `(3)`.
-/

open CategoryTheory Limits

namespace RHTower

universe wS wT wA vS vT vA uS uT uA

section Adjunction

variable {S : Type uS} {T : Type uT} [Category.{vS} S] [Category.{vT} T]

/-- **An exact left adjoint makes the coarse pushforward preserve injectives.**  Deninger's
`c_* = (π_* −)^G` is right adjoint to the pullback `c^*`, and the pullback is exact; a right
adjoint of a monomorphism-preserving functor sends injective objects to injective objects, which
is the input Grothendieck's composition law needs. -/
theorem deningerCoarsePushforward_preservesInjectives
    {cStar : S ⥤ T} {cUpper : T ⥤ S} (adj : cUpper ⊣ cStar)
    [PreservesFiniteLimits cUpper] : cStar.PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

end Adjunction

section CoarseStack

variable {S : Type uS} {T : Type uT} {A : Type uA}
  [Category.{vS} S] [Category.{vT} T] [Category.{vA} A]
  [Abelian S] [Abelian T] [Abelian A]
  [HasDerivedCategory.{wS} S] [HasDerivedCategory.{wT} T] [HasDerivedCategory.{wA} A]
  [EnoughInjectives S] [EnoughInjectives T]

variable (cStar : S ⥤ T) [cStar.Additive]

/-- **The canonical comparison `(2)`** `c_* Ã ⟶ R c_* Ã`, evaluated at a bounded below
`G`-equivariant coefficient complex `Ã`.  Its source is the underived, degreewise invariant
coefficient of `(1)` seen in the derived category, and its target is the derived pushforward. -/
noncomputable def deningerCoarseComparison (Atilde : HomotopyCategory.Plus S) :
    DerivedCategory.Plus.Qh.obj (cStar.mapHomotopyCategoryPlus.obj Atilde) ⟶
      cStar.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj Atilde) :=
  cStar.rightDerivedFunctorPlusUnit.app Atilde

variable (Gamma : T ⥤ A) [Gamma.Additive]

/-- **Global sections on the quotient stack.**  By Deninger's definition `(1)` of the invariant
coefficient, sections over the stack are the coarse sections of the invariant pushforward, so the
stack's global-sections functor is `Γ_X ∘ c_*`. -/
noncomputable abbrev deningerStackGlobalSections : S ⥤ A := cStar ⋙ Gamma

variable [cStar.PreservesInjectiveObjects]

/-- **Derived descent for the quotient stack.**  The derived global sections of the stack are the
derived coarse global sections of the derived pushforward.  This is Grothendieck's composition law
applied to `Γ_{[X̃/G]} = Γ_X ∘ c_*`, legitimate because `c_*` preserves injective objects. -/
noncomputable def deningerDerivedDescentIso :
    (deningerStackGlobalSections cStar Gamma).rightDerivedFunctorPlus ≅
      cStar.rightDerivedFunctorPlus ⋙ Gamma.rightDerivedFunctorPlus :=
  HTGeometry.rightDerivedFunctorPlusCompIso cStar Gamma

/-- **Equation `(3)`: the derived-topos comparison.**  If the canonical comparison `(2)` is a
quasi-isomorphism at `Ã`, then applying `RΓ(X, −)` to it and using derived descent for the
quotient stack gives an isomorphism

`RΓ(X, c_* Ã) ≅ RΓ([X̃/G], Ã)`

in the bounded below derived category.  This is the step that transports the scalar rational-time
action on stack `H¹` to Deninger's `H¹`. -/
noncomputable def deningerDerivedToposComparisonIso (Atilde : HomotopyCategory.Plus S)
    (hcomp : IsIso (deningerCoarseComparison cStar Atilde)) :
    Gamma.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj (cStar.mapHomotopyCategoryPlus.obj Atilde)) ≅
      (deningerStackGlobalSections cStar Gamma).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj Atilde) :=
  Gamma.rightDerivedFunctorPlus.mapIso (asIso (deningerCoarseComparison cStar Atilde)) ≪≫
    (HTGeometry.rightDerivedFunctorPlusCompObjIso cStar Gamma
      (DerivedCategory.Plus.Qh.obj Atilde)).symm

/-- The same comparison packaged with the adjunction hypothesis in place of the abstract
preservation of injectives: an exact pullback is all that is needed. -/
theorem deningerDerivedToposComparison_nonempty (Atilde : HomotopyCategory.Plus S)
    (hcomp : IsIso (deningerCoarseComparison cStar Atilde)) :
    Nonempty (Gamma.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj (cStar.mapHomotopyCategoryPlus.obj Atilde)) ≅
      (deningerStackGlobalSections cStar Gamma).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj Atilde)) :=
  ⟨deningerDerivedToposComparisonIso cStar Gamma Atilde hcomp⟩

end CoarseStack

end RHTower

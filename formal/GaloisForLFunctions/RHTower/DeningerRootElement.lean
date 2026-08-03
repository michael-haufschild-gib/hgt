import GaloisForLFunctions.RHTower.DeningerRootTwo

/-!
# The adjoined root

The amalgam of a group with an infinite cyclic group over an infinite cyclic base, glued along `a`
and the `m`-th power of the generator, contains the group and an `m`-th root of `a`.

* `deningerRootElt` : the adjoined root.
* `deningerRootElt_zpow` : it is an `m`-th root of `a`.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- The generator of the infinite cyclic factor. -/
noncomputable def deningerRootGen : ULift.{u} (Multiplicative ℤ) :=
  MulEquiv.ulift.symm (Multiplicative.ofAdd (1 : ℤ))

theorem deningerUliftZpow_gen (m : ℤ)
    (f : ULift.{u} (Multiplicative ℤ) →* ULift.{u} (Multiplicative ℤ))
    (hf : f = (MulEquiv.ulift.symm.toMonoidHom).comp
      ((zpowGroupHom m).comp MulEquiv.ulift.toMonoidHom)) :
    f deningerRootGen.{u} = deningerRootGen.{u} ^ m := by
  subst hf
  show MulEquiv.ulift.symm ((MulEquiv.ulift deningerRootGen.{u}) ^ m) = _
  rw [deningerRootGen, map_zpow]
  simp

theorem deningerUliftZpowers_gen (A : Type u) [Group A] (a : A)
    (f : ULift.{u} (Multiplicative ℤ) →* A)
    (hf : f = (zpowersHom A a).comp MulEquiv.ulift.toMonoidHom) :
    f deningerRootGen.{u} = a := by
  subst hf
  show (zpowersHom A a) (MulEquiv.ulift deningerRootGen.{u}) = a
  rw [deningerRootGen]
  simp

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- **The adjoined root.** -/
noncomputable def deningerRootElt : PushoutI (deningerRootMap A a m) :=
  PushoutI.of (ULift.up false) deningerRootGen.{u}

theorem deningerRootMap_false_gen :
    deningerRootMap A a m (ULift.up false) deningerRootGen.{u} = deningerRootGen.{u} ^ m :=
  deningerUliftZpow_gen m _ rfl

theorem deningerRootMap_true_gen :
    deningerRootMap A a m (ULift.up true) deningerRootGen.{u} = a :=
  deningerUliftZpowers_gen A a _ rfl

/-- **The adjoined element is an `m`-th root of `a`.** -/
theorem deningerRootElt_zpow :
    (deningerRootElt A a m) ^ m = PushoutI.of (ULift.up true) a := by
  have h1 : (deningerRootElt A a m) ^ m =
      PushoutI.of (ULift.up false)
        (deningerRootMap A a m (ULift.up false) deningerRootGen.{u}) := by
    rw [deningerRootElt, ← map_zpow]
    congr 1
  rw [h1, PushoutI.of_apply_eq_base]
  have h2 : PushoutI.of (ULift.up true)
        (deningerRootMap A a m (ULift.up true) deningerRootGen.{u}) =
      PushoutI.base (deningerRootMap A a m) deningerRootGen.{u} :=
    PushoutI.of_apply_eq_base _ _ _
  rw [← h2]
  congr 1
  exact deningerRootMap_true_gen A a m

end RootAdjunction

end RHTower

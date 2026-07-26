import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Fintype.Option
import Mathlib.Data.ZMod.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Group-like and cyclotomic extensions of the field-one core

Adjoining zero to an abelian group gives every group-like extension of the
multiplicative field-one core. Contracted scalar extension gives the associated
group algebra. Cyclic groups produce the traditional `F_(1^n)` family.
-/

namespace GaloisForLFunctions.HTGeometry.FieldOneCore

/-- Adjoin an absorbing zero to an abelian group. -/
abbrev FieldOneGroupExtension (G : Type*) [CommGroup G] := WithZero G

/-- The unit group of a group-like field-one extension is the original group. -/
def groupExtensionUnitsEquiv (G : Type*) [CommGroup G] :
    (FieldOneGroupExtension G)ˣ ≃* G :=
  WithZero.unitsWithZeroEquiv

/-- Every commutative group with zero is zero adjoined to its unit group. -/
noncomputable def commGroupWithZeroClassification (K : Type*) [CommGroupWithZero K] :
    WithZero Kˣ ≃* K := by
  classical
  exact WithZero.withZeroUnitsEquiv

/-- Every nonzero element of a group-like extension is a unit. -/
theorem groupExtension_isUnit_of_ne_zero {G : Type*} [CommGroup G]
    {x : FieldOneGroupExtension G} (hx : x ≠ 0) : IsUnit x := by
  induction x using WithZero.recZeroCoe with
  | zero => exact False.elim (hx rfl)
  | coe g => exact isUnit_iff_ne_zero.mpr WithZero.coe_ne_zero

/-- Contracted scalar extension of a group-like field-one extension is its group algebra. -/
abbrev GroupExtensionBaseChange (R G : Type*) [CommSemiring R] [CommGroup G] :=
  MonoidAlgebra R G

/-- Cyclotomic field-one extension with cyclic nonzero unit group. -/
abbrev CyclotomicFieldOne (n : ℕ) :=
  FieldOneGroupExtension (Multiplicative (ZMod n))

/-- The cyclotomic extension has `n` units and one absorbing zero. -/
theorem card_cyclotomicFieldOne (n : ℕ) [NeZero n] :
    Nat.card (CyclotomicFieldOne n) = n + 1 := by
  letI : Fintype (CyclotomicFieldOne n) :=
    inferInstanceAs (Fintype (Option (Multiplicative (ZMod n))))
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Option (Multiplicative (ZMod n))) = n + 1
  rw [Fintype.card_option, Fintype.card_multiplicative, ZMod.card]

/-- Contracted base extension of `F_(1^n)` is the cyclic group algebra. -/
abbrev CyclotomicBaseChange (R : Type*) [CommSemiring R] (n : ℕ) :=
  MonoidAlgebra R (Multiplicative (ZMod n))

end GaloisForLFunctions.HTGeometry.FieldOneCore

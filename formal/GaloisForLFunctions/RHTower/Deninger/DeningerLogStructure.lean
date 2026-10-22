import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# Prelog and log structures on a commutative ring

A prelog structure on a commutative ring is a commutative monoid with a multiplicative map to the
ring; it is a log structure when that map identifies the part lying over the units with the units
themselves.  The characteristic monoid of a log structure is the quotient by that part, and it is
presented here by a characteristic map: a monoid map whose kernel is exactly the part over the
units and whose fibres are its orbits.

* `DeningerPreLog`, `DeningerIsLog` : the definitions.
* `DeningerLogChar` : a presentation of the characteristic monoid.
* `deningerLogChar_eq_iff` : two sections have the same character exactly when they differ by a
  unit.
-/

namespace RHTower

universe u v

/-- A prelog structure on a commutative ring: a commutative monoid with a multiplicative map to the
ring. -/
structure DeningerPreLog (R : Type u) [CommRing R] where
  /-- The monoid of the prelog structure. -/
  M : Type u
  /-- Its monoid structure. -/
  [commMonoid : CommMonoid M]
  /-- The structure map to the multiplicative monoid of the ring. -/
  hom : M →* R

attribute [instance] DeningerPreLog.commMonoid

/-- A prelog structure is a **log structure** when the part lying over the units maps bijectively
onto the units. -/
structure DeningerIsLog {R : Type u} [CommRing R] (L : DeningerPreLog R) : Prop where
  /-- The map is injective on the part lying over the units. -/
  injOn : ∀ ⦃m n : L.M⦄, IsUnit (L.hom m) → IsUnit (L.hom n) → L.hom m = L.hom n → m = n
  /-- Every unit is hit. -/
  surjOn : ∀ r : R, IsUnit r → ∃ m : L.M, L.hom m = r

/-- **A presentation of the characteristic monoid** of a log structure: a monoid map whose kernel is
the part lying over the units, whose fibres are the orbits of that part, and which is onto. -/
structure DeningerLogChar {R : Type u} [CommRing R] (L : DeningerPreLog R) (N : Type v)
    [CommMonoid N] where
  /-- The characteristic map. -/
  ord : L.M →* N
  /-- It is onto. -/
  surj : Function.Surjective ord
  /-- Its kernel is the part lying over the units. -/
  ker : ∀ m : L.M, ord m = 1 ↔ IsUnit (L.hom m)
  /-- Its fibres are the orbits of that part. -/
  orbit : ∀ m n : L.M, ord m = ord n → ∃ w : L.M, IsUnit (L.hom w) ∧ m = n * w

variable {R : Type u} [CommRing R] {L : DeningerPreLog R} {N : Type v} [CommMonoid N]

/-- **Two sections have the same character exactly when they differ by a section over a unit.** -/
theorem deningerLogChar_eq_iff (C : DeningerLogChar L N) (m n : L.M) :
    C.ord m = C.ord n ↔ ∃ w : L.M, IsUnit (L.hom w) ∧ m = n * w := by
  refine ⟨C.orbit m n, ?_⟩
  rintro ⟨w, hw, rfl⟩
  rw [map_mul, (C.ker w).2 hw, mul_one]

/-- **The character of a section over a unit is trivial.** -/
theorem deningerLogChar_unit (C : DeningerLogChar L N) {m : L.M} (hm : IsUnit (L.hom m)) :
    C.ord m = 1 := (C.ker m).2 hm

end RHTower

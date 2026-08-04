import GaloisForLFunctions.RHTower.DeningerLogStructure
import Mathlib.Algebra.Group.PUnit
import Mathlib.Tactic.Group

/-!
# The trivial log structure

The units of a commutative ring form a log structure whose characteristic monoid is trivial, and
conversely a log structure whose characteristic monoid is trivial has every section lying over a
unit.  So triviality of the characteristic monoid is exactly the statement that the log structure
carries no divisorial information.

* `deningerTrivialLog` : the trivial log structure.
* `deningerTrivialChar` : its characteristic monoid is trivial.
* `deningerLogChar_subsingleton_iff` : the characteristic monoid is trivial exactly when every
  section lies over a unit.
-/

namespace RHTower

universe u v

variable (R : Type u) [CommRing R]

/-- **The trivial log structure**: the units of the ring, included into the ring. -/
def deningerTrivialLog : DeningerPreLog R where
  M := Rˣ
  hom := Units.coeHom R

@[simp]
theorem deningerTrivialLog_hom (u : Rˣ) : (deningerTrivialLog R).hom u = (u : R) := rfl

/-- **The trivial log structure is a log structure.** -/
theorem deningerTrivialLog_isLog : DeningerIsLog (deningerTrivialLog R) where
  injOn := by
    intro m n _ _ h
    exact Units.ext h
  surjOn := by
    intro r hr
    exact ⟨hr.unit, hr.unit_spec⟩

/-- Any two units differ by a unit. -/
theorem deningerTrivialLog_orbit (m n : Rˣ) : ∃ w : Rˣ, IsUnit ((w : R)) ∧ m = n * w :=
  ⟨n⁻¹ * m, ⟨n⁻¹ * m, rfl⟩, by group⟩

/-- **The characteristic monoid of the trivial log structure is trivial.** -/
def deningerTrivialChar : DeningerLogChar (deningerTrivialLog R) PUnit.{v + 1} where
  ord := 1
  surj := fun _ => ⟨1, Subsingleton.elim _ _⟩
  ker := fun m => ⟨fun _ => ⟨m, rfl⟩, fun _ => Subsingleton.elim _ _⟩
  orbit := fun m n _ => deningerTrivialLog_orbit R m n

variable {R}

/-- **The characteristic monoid is trivial exactly when every section lies over a unit.** -/
theorem deningerLogChar_subsingleton_iff {L : DeningerPreLog R} {N : Type v} [CommMonoid N]
    (C : DeningerLogChar L N) :
    Subsingleton N ↔ ∀ m : L.M, IsUnit (L.hom m) := by
  constructor
  · intro h m
    exact (C.ker m).1 (Subsingleton.elim _ _)
  · intro h
    refine ⟨fun a b => ?_⟩
    obtain ⟨m, rfl⟩ := C.surj a
    obtain ⟨n, rfl⟩ := C.surj b
    rw [(C.ker m).2 (h m), (C.ker n).2 (h n)]

end RHTower

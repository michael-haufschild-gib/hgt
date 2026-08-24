import Mathlib

/-!
# Jointly separating Hasse families

A Hasse family is a dependent family of local observations whose complete profile separates
global objects.  The abstraction supplies the common consequences used throughout local--global
arguments: equivalence with realized profiles, pointwise congruence, and a local witness for every
global inequality.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- A family of local observations which jointly separates global objects. -/
structure HasseFamily (G : Type u) (ι : Type v) where
  Local : ι → Type w
  profile : G → ((i : ι) → Local i)
  profile_injective : Function.Injective profile

namespace HasseFamily

variable {G : Type u} {ι : Type v} (H : HasseFamily G ι)

/-- Global objects are equivalent to the local profiles that actually occur. -/
noncomputable def equivRealizedProfiles : G ≃ Set.range H.profile :=
  Equiv.ofInjective H.profile H.profile_injective

/-- The realized-profile equivalence evaluates as the original local profile. -/
@[simp] theorem equivRealizedProfiles_apply (x : G) :
    (H.equivRealizedProfiles x).1 = H.profile x := rfl

/-- Equality of complete profiles is equivalent to global equality. -/
theorem profile_eq_iff (x y : G) : H.profile x = H.profile y ↔ x = y :=
  H.profile_injective.eq_iff

/-- Global equality can be checked one local coordinate at a time. -/
theorem pointwise_eq_iff (x y : G) :
    (∀ i, H.profile x i = H.profile y i) ↔ x = y := by
  rw [← H.profile_eq_iff]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- Distinct global objects are separated by at least one local coordinate. -/
theorem exists_local_ne_of_ne {x y : G} (hxy : x ≠ y) :
    ∃ i, H.profile x i ≠ H.profile y i := by
  by_contra h
  push Not at h
  exact hxy ((H.pointwise_eq_iff x y).mp h)

/-- Local separation is exactly global inequality. -/
theorem ne_iff_exists_local_ne (x y : G) :
    x ≠ y ↔ ∃ i, H.profile x i ≠ H.profile y i := by
  constructor
  · exact H.exists_local_ne_of_ne
  · rintro ⟨i, hi⟩ rfl
    exact hi rfl

/-- Build a Hasse family from a single injective dependent product-valued profile. -/
def ofInjective (L : ι → Type w) (profile : G → ((i : ι) → L i))
    (hprofile : Function.Injective profile) : HasseFamily G ι where
  Local := L
  profile := profile
  profile_injective := hprofile

/-- An equivalence with a full dependent product supplies a Hasse family. -/
def ofEquivFunctions (L : ι → Type w) (e : G ≃ ((i : ι) → L i)) :
    HasseFamily G ι where
  Local := L
  profile := e
  profile_injective := e.injective

/-- An equivalence with a subtype of dependent functions supplies a Hasse family by forgetting
the realization certificate at each place. -/
def ofEquivSubtypeFunctions (L : ι → Type w)
    (S : Set ((i : ι) → L i)) (e : G ≃ S) : HasseFamily G ι where
  Local := L
  profile := fun x => (e x).1
  profile_injective := by
    intro x y hxy
    apply e.injective
    exact Subtype.ext hxy

/-- A single complete local invariant supplies a one-place Hasse family. -/
def ofEquivSingle {L : Type w} (e : G ≃ L) : HasseFamily G Unit where
  Local := fun _ => L
  profile := fun x _ => e x
  profile_injective := by
    intro x y hxy
    apply e.injective
    exact congrFun hxy ()

end HasseFamily

end GaloisForLFunctions.HTGeometry

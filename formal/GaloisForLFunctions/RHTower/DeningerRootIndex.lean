import GaloisForLFunctions.RHTower.DeningerBaseInFactor

/-!
# The index of a root adjunction

The base group of a root adjunction sits in the infinite cyclic factor as the `m`-th powers, so its
index there is the absolute value of `m`.

* `deningerZpowRange` : the `m`-th powers of an infinite cyclic group.
* `deningerRootMap_range_index` : the index.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

theorem deningerZpowRange (m : ℤ) :
    ((zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ)).range =
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples m) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Multiplicative.toAdd y, by simp [zpowGroupHom, mul_comm]⟩
  · rintro ⟨k, hk⟩
    exact ⟨Multiplicative.ofAdd k, by
      simp only [zpowGroupHom, MonoidHom.coe_mk, OneHom.coe_mk]
      apply Multiplicative.toAdd.injective
      simpa [mul_comm] using hk⟩

/-- The index of the `m`-th powers of an infinite cyclic group. -/
theorem deningerUliftZpow_index (m : ℤ)
    (f : ULift.{u} (Multiplicative ℤ) →* ULift.{u} (Multiplicative ℤ))
    (hf : f = (MulEquiv.ulift.symm.toMonoidHom).comp
      ((zpowGroupHom m).comp MulEquiv.ulift.toMonoidHom)) :
    (f.range).index = m.natAbs := by
  subst hf
  have hcomap : (((MulEquiv.ulift.symm.toMonoidHom).comp
        ((zpowGroupHom m).comp MulEquiv.ulift.toMonoidHom)).range) =
      Subgroup.comap
        (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ).toMonoidHom
        ((zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ)).range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨MulEquiv.ulift y, rfl⟩
    · rintro ⟨z, hz⟩
      refine ⟨MulEquiv.ulift.symm z, ?_⟩
      apply MulEquiv.ulift.injective
      exact hz
  rw [hcomap, Subgroup.index_comap_of_surjective _ MulEquiv.ulift.surjective,
    deningerZpowRange, AddSubgroup.index_toSubgroup, Int.index_zmultiples]

/-- **The base group of a root adjunction has index `|m|` in the infinite cyclic factor.** -/
theorem deningerRootMap_range_index (A : Type u) [Group A] (a : A) (m : ℤ) :
    ((deningerRootMap A a m (ULift.up false)).range).index = m.natAbs :=
  deningerUliftZpow_index m _ rfl

end RootAdjunction

end RHTower

import GaloisForLFunctions.RHTower.Deninger.DeningerUniqueRootsTransport

/-!
# A free group is an amalgam of infinite cyclic groups over the trivial group

The free group on a set and the pushout of copies of the infinite cyclic group over the trivial
group have the same universal property, so the two homomorphisms built from those properties are
mutually inverse: one is checked on the generators, the other on the factors.

* `deningerFreeFactor`, `deningerFreeMap` : the amalgam data.
* `deningerFreeGroupEquiv` : the isomorphism.
-/

namespace RHTower

open Monoid Monoid.PushoutI RootAdjunction

universe u

/-- The factors of a free group as an amalgam: copies of the infinite cyclic group. -/
def deningerFreeFactor (ι : Type u) : ι → Type u := fun _ => ULift.{u} (Multiplicative ℤ)

instance deningerFreeFactorGroup (ι : Type u) : ∀ i, Group (deningerFreeFactor ι i) :=
  fun _ => inferInstanceAs (Group (ULift.{u} (Multiplicative ℤ)))

/-- The structure maps of a free group as an amalgam: all trivial. -/
def deningerFreeMap (ι : Type u) : ∀ i, PUnit.{u + 1} →* deningerFreeFactor ι i := fun _ => 1

/-- The map from the free group to the amalgam. -/
noncomputable def deningerFreeToPushout (ι : Type u) :
    FreeGroup ι →* PushoutI (deningerFreeMap ι) :=
  FreeGroup.lift (fun i => PushoutI.of (φ := deningerFreeMap ι) i deningerRootGen.{u})

/-- The map from the amalgam to the free group. -/
noncomputable def deningerPushoutToFree (ι : Type u) :
    PushoutI (deningerFreeMap ι) →* FreeGroup ι :=
  PushoutI.lift (fun i => (zpowersHom (FreeGroup ι) (FreeGroup.of i)).comp
      (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ).toMonoidHom) 1
    (fun i => MonoidHom.ext fun x => by
      rw [Subsingleton.elim x 1, map_one, map_one])

theorem deningerPushoutToFree_of (ι : Type u) (i : ι) (x : deningerFreeFactor ι i) :
    deningerPushoutToFree ι (PushoutI.of (φ := deningerFreeMap ι) i x) =
      (FreeGroup.of i) ^ (Multiplicative.toAdd (MulEquiv.ulift x)) := by
  rw [deningerPushoutToFree, PushoutI.lift_of]
  rfl

theorem deningerFreeToPushout_of (ι : Type u) (i : ι) :
    deningerFreeToPushout ι (FreeGroup.of i) =
      PushoutI.of (φ := deningerFreeMap ι) i deningerRootGen.{u} := by
  rw [deningerFreeToPushout, FreeGroup.lift_apply_of]

/-- Every element of a factor is a power of the generator. -/
theorem deningerFreeFactor_zpow (ι : Type u) (i : ι) (x : deningerFreeFactor ι i) :
    deningerRootGen.{u} ^ (Multiplicative.toAdd (MulEquiv.ulift x)) = x := by
  apply MulEquiv.ulift.injective
  apply Multiplicative.toAdd.injective
  simp [deningerRootGen]

/-- The two maps compose to the identity on the free group. -/
theorem deningerFreeToPushout_comp (ι : Type u) :
    (deningerPushoutToFree ι).comp (deningerFreeToPushout ι) = MonoidHom.id (FreeGroup ι) := by
  refine FreeGroup.ext_hom _ _ (fun i => ?_)
  rw [MonoidHom.comp_apply, deningerFreeToPushout_of, deningerPushoutToFree_of]
  simp [deningerRootGen]

/-- The two maps compose to the identity on the amalgam. -/
theorem deningerPushoutToFree_comp (ι : Type u) :
    (deningerFreeToPushout ι).comp (deningerPushoutToFree ι) =
      MonoidHom.id (PushoutI (deningerFreeMap ι)) := by
  refine PushoutI.hom_ext (fun i => MonoidHom.ext fun x => ?_) (MonoidHom.ext fun x => ?_)
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, deningerPushoutToFree_of, map_zpow,
      deningerFreeToPushout_of, ← map_zpow]
    exact congrArg (PushoutI.of (φ := deningerFreeMap ι) i) (deningerFreeFactor_zpow ι i x)
  · have h1 : PushoutI.base (deningerFreeMap ι) x = 1 := by
      rw [Subsingleton.elim x 1, map_one]
    simp [MonoidHom.comp_apply, h1]

/-- **A free group is an amalgam of infinite cyclic groups over the trivial group.** -/
noncomputable def deningerFreeGroupEquiv (ι : Type u) :
    FreeGroup ι ≃* PushoutI (deningerFreeMap ι) where
  toFun := deningerFreeToPushout ι
  invFun := deningerPushoutToFree ι
  left_inv := DFunLike.congr_fun (deningerFreeToPushout_comp ι)
  right_inv := DFunLike.congr_fun (deningerPushoutToFree_comp ι)
  map_mul' := map_mul _

end RHTower

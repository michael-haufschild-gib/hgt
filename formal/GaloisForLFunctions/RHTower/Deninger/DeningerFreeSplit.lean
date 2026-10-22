import GaloisForLFunctions.RHTower.Deninger.DeningerFreeGroupAmalgam
import GaloisForLFunctions.RHTower.Deninger.DeningerTreeVanishing

/-!
# Splitting off one generator of a free group

Adding one element to the index set of a free group is a free product with the infinite cyclic
group, amalgamated over the trivial group.  Both maps are checked on the generators and on the
factors.

* `deningerFreeSplitFactor`, `deningerFreeSplitMap` : the two factor amalgam.
* `deningerFreeSplitEquiv` : the isomorphism.
-/

namespace RHTower

open Monoid Monoid.PushoutI RootAdjunction

universe u

/-- The two factors of the splitting: the free group on the old index set, and an infinite cyclic
group for the new generator. -/
def deningerFreeSplitFactor (α : Type u) : ULift.{u} Bool → Type u :=
  fun i => bif i.down then FreeGroup α else ULift.{u} (Multiplicative ℤ)

instance deningerFreeSplitFactorGroup (α : Type u) :
    ∀ i, Group (deningerFreeSplitFactor α i)
  | ⟨true⟩ => inferInstanceAs (Group (FreeGroup α))
  | ⟨false⟩ => inferInstanceAs (Group (ULift.{u} (Multiplicative ℤ)))

/-- The structure maps of the splitting: all trivial. -/
def deningerFreeSplitMap (α : Type u) :
    ∀ i, PUnit.{u + 1} →* deningerFreeSplitFactor α i := fun _ => 1

theorem deningerFreeSplitMap_injective (α : Type u) :
    ∀ i, Function.Injective (deningerFreeSplitMap α i) := by
  intro i x y _
  exact Subsingleton.elim x y

/-- The generator of the new factor. -/
noncomputable def deningerFreeSplitGen (α : Type u) :
    deningerFreeSplitFactor α (ULift.up false) := deningerRootGen.{u}

/-- The map from the free group on the enlarged index set to the amalgam. -/
noncomputable def deningerFreeSplitTo (α : Type u) :
    FreeGroup (Option α) →* PushoutI (deningerFreeSplitMap α) :=
  FreeGroup.lift (fun i => match i with
    | none => PushoutI.of (φ := deningerFreeSplitMap α) (ULift.up false) (deningerFreeSplitGen α)
    | some a => PushoutI.of (φ := deningerFreeSplitMap α) (ULift.up true)
        (show FreeGroup α from FreeGroup.of a))

/-- The map from the amalgam to the free group on the enlarged index set. -/
noncomputable def deningerFreeSplitFrom (α : Type u) :
    PushoutI (deningerFreeSplitMap α) →* FreeGroup (Option α) :=
  PushoutI.lift
    (fun i => match i with
      | ⟨true⟩ => show deningerFreeSplitFactor α (ULift.up true) →* FreeGroup (Option α) from
          FreeGroup.map some
      | ⟨false⟩ => show deningerFreeSplitFactor α (ULift.up false) →* FreeGroup (Option α) from
          (zpowersHom (FreeGroup (Option α)) (FreeGroup.of none)).comp
            (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ).toMonoidHom)
    1
    (fun i => MonoidHom.ext fun x => by
      rw [Subsingleton.elim x 1, map_one, map_one])

theorem deningerFreeSplitFrom_true (α : Type u) (x : FreeGroup α) :
    deningerFreeSplitFrom α (PushoutI.of (φ := deningerFreeSplitMap α) (ULift.up true) x) =
      FreeGroup.map some x := by
  rw [deningerFreeSplitFrom, PushoutI.lift_of]
  rfl

theorem deningerFreeSplitFrom_false (α : Type u)
    (x : deningerFreeSplitFactor α (ULift.up false)) :
    deningerFreeSplitFrom α (PushoutI.of (φ := deningerFreeSplitMap α) (ULift.up false) x) =
      (FreeGroup.of (none : Option α)) ^ (Multiplicative.toAdd (MulEquiv.ulift x)) := by
  rw [deningerFreeSplitFrom, PushoutI.lift_of]
  rfl

/-- Every element of the new factor is a power of its generator. -/
theorem deningerFreeSplitFactor_zpow (α : Type u)
    (x : deningerFreeSplitFactor α (ULift.up false)) :
    (deningerFreeSplitGen α) ^ (Multiplicative.toAdd (MulEquiv.ulift x)) = x :=
  deningerFreeFactor_zpow PUnit.{u + 1} PUnit.unit x

/-- The two maps compose to the identity on the free group. -/
theorem deningerFreeSplitTo_comp (α : Type u) :
    (deningerFreeSplitFrom α).comp (deningerFreeSplitTo α) =
      MonoidHom.id (FreeGroup (Option α)) := by
  refine FreeGroup.ext_hom _ _ (fun i => ?_)
  cases i with
  | none =>
    rw [MonoidHom.comp_apply, deningerFreeSplitTo, FreeGroup.lift_apply_of,
      deningerFreeSplitFrom_false]
    simp [deningerFreeSplitGen, deningerRootGen]
  | some a =>
    rw [MonoidHom.comp_apply, deningerFreeSplitTo, FreeGroup.lift_apply_of,
      deningerFreeSplitFrom_true]
    simp

/-- The two maps compose to the identity on the amalgam. -/
theorem deningerFreeSplitFrom_comp (α : Type u) :
    (deningerFreeSplitTo α).comp (deningerFreeSplitFrom α) =
      MonoidHom.id (PushoutI (deningerFreeSplitMap α)) := by
  refine PushoutI.hom_ext (fun i => ?_) (MonoidHom.ext fun x => ?_)
  · obtain ⟨b⟩ := i
    cases b
    · refine MonoidHom.ext fun x => ?_
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [deningerFreeSplitFrom_false, map_zpow, deningerFreeSplitTo, FreeGroup.lift_apply_of,
        ← map_zpow]
      exact congrArg (PushoutI.of (φ := deningerFreeSplitMap α) (ULift.up false))
        (deningerFreeSplitFactor_zpow α x)
    · refine MonoidHom.ext fun x => ?_
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [deningerFreeSplitFrom_true]
      refine FreeGroup.induction_on (C := fun y : FreeGroup α =>
        deningerFreeSplitTo α (FreeGroup.map some y) =
          PushoutI.of (φ := deningerFreeSplitMap α) (ULift.up true) y) x ?_ ?_ ?_ ?_
      · rw [map_one, map_one]
        exact (map_one _).symm
      · intro a
        rw [FreeGroup.map.of, deningerFreeSplitTo, FreeGroup.lift_apply_of]
      · intro a hy
        rw [map_inv, map_inv, hy, ← map_inv]
        rfl
      · intro y z hy hz
        rw [map_mul, map_mul, hy, hz, ← map_mul]
        rfl
  · have h1 : PushoutI.base (deningerFreeSplitMap α) x = 1 := by
      rw [Subsingleton.elim x 1, map_one]
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [h1]
    exact map_one _

/-- **Adding a generator to a free group is a free product with an infinite cyclic group.** -/
noncomputable def deningerFreeSplitEquiv (α : Type u) :
    FreeGroup (Option α) ≃* PushoutI (deningerFreeSplitMap α) where
  toFun := deningerFreeSplitTo α
  invFun := deningerFreeSplitFrom α
  left_inv := DFunLike.congr_fun (deningerFreeSplitTo_comp α)
  right_inv := DFunLike.congr_fun (deningerFreeSplitFrom_comp α)
  map_mul' := map_mul _

end RHTower

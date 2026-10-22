import GaloisForLFunctions.RHTower.Deninger.DeningerBauVanishingCriterion
import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagGeneration

/-!
# The rationalization of a trivial group

The rationalization of a group with one element has one element: the trivial subgroup is closed
under the roots, because the only root of the identity is the identity.  So the packet's homology
vanishes in every positive degree when the index set is empty.

* `deningerBau_subsingleton` : the rationalization of a subsingleton group.
* `deningerBauFree_isZero_of_isEmpty` : the vanishing for an empty index set.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

variable {α : Type u} [Group α]

/-- **The rationalization of a group with one element has one element.** -/
theorem deningerBau_subsingleton [Subsingleton α] : Subsingleton (DeningerBau α) := by
  have hbot : (⊥ : Subgroup (DeningerBau α)) = ⊤ := by
    refine DeningerBau.eq_top_of_rootClosed _ (fun n x hx => ?_) (fun a => ?_)
    · rw [Subgroup.mem_bot] at hx
      subst hx
      rw [Subgroup.mem_bot]
      refine DeningerBau.torsionFree _ (n + 1) (by omega) ?_
      rw [DeningerBau.root_pow]
    · rw [Subgroup.mem_bot, Subsingleton.elim a 1, map_one]
  constructor
  intro x y
  have hx : x ∈ (⊥ : Subgroup (DeningerBau α)) := by rw [hbot]; trivial
  have hy : y ∈ (⊥ : Subgroup (DeningerBau α)) := by rw [hbot]; trivial
  rw [Subgroup.mem_bot] at hx hy
  rw [hx, hy]

/-- **The packet's homology vanishes in positive degrees for an empty index set.** -/
theorem deningerBauFree_isZero_of_isEmpty (k : Type u) [CommRing k] {ι : Type u} [IsEmpty ι]
    (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k (DeningerBau (FreeGroup ι)) k) (n + 1)) := by
  haveI : Subsingleton (FreeGroup ι) := by
    constructor
    intro x y
    have h : (MonoidHom.id (FreeGroup ι)) = (1 : FreeGroup ι →* FreeGroup ι) :=
      FreeGroup.ext_hom _ _ (fun i => (IsEmpty.false i).elim)
    have hx := congrArg (fun f : FreeGroup ι →* FreeGroup ι => f x) h
    have hy := congrArg (fun f : FreeGroup ι →* FreeGroup ι => f y) h
    simp only [MonoidHom.id_apply, MonoidHom.one_apply] at hx hy
    rw [hx, hy]
  haveI : Subsingleton (DeningerBau (FreeGroup ι)) := deningerBau_subsingleton
  exact isZero_groupHomology_succ_of_subsingleton _ n

end RHTower

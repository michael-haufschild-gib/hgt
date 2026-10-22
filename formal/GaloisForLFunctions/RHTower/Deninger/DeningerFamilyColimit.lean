import GaloisForLFunctions.RHTower.Deninger.DeningerFamilyTower
import GaloisForLFunctions.RHTower.Deninger.DeningerChainUniqueRoots
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The colimit of the tower over a family

The chain of stages and embeddings is a functor out of the natural numbers, and its filtered colimit
is a group in which every element comes from a stage and no stage is collapsed.  Unique roots
transport to it from the stages.

* `deningerFamilyColimit` : the colimit.
* `deningerFamilyColimit_uniqueRoots` : it has unique roots.
-/

namespace RHTower

open CategoryTheory Monoid

universe u

namespace RootAdjunction

/-- The tower over a family, as a functor. -/
noncomputable def deningerFamilyDiagram (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) :
    ℕ ⥤ GrpCat.{u} :=
  Functor.ofSequence (X := fun n => GrpCat.of ((deningerFamilyTower S₀ sched n).carrier))
    (fun n => GrpCat.ofHom (deningerFamilyEmbed S₀ sched n))

/-- **The colimit of the tower over a family.** -/
noncomputable def deningerFamilyColimit (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) :
    GrpCat.{u} :=
  GrpCat.FilteredColimits.colimit (deningerFamilyDiagram S₀ sched)

/-- The structure map of a stage into the colimit. -/
noncomputable def deningerFamilyIota (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) (n : ℕ) :
    (deningerFamilyTower S₀ sched n).carrier →* (deningerFamilyColimit S₀ sched) :=
  ((GrpCat.FilteredColimits.colimitCocone (deningerFamilyDiagram S₀ sched)).ι.app n).hom

/-- **Every element of the colimit comes from a stage.** -/
theorem deningerFamilyColimit_surjective (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ)
    (x : deningerFamilyColimit S₀ sched) :
    ∃ (n : ℕ) (a : (deningerFamilyTower S₀ sched n).carrier),
      deningerFamilyIota S₀ sched n a = x := by
  refine Quot.inductionOn x ?_
  rintro ⟨n, a⟩
  exact ⟨n, a, rfl⟩

/-- **The structure maps are compatible with the embeddings.** -/
theorem deningerFamilyIota_step (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) (n : ℕ)
    (x : (deningerFamilyTower S₀ sched n).carrier) :
    deningerFamilyIota S₀ sched (n + 1) (deningerFamilyEmbed S₀ sched n x) =
      deningerFamilyIota S₀ sched n x := by
  have h := (GrpCat.FilteredColimits.colimitCocone (deningerFamilyDiagram S₀ sched)).w
    (homOfLE (Nat.le_succ n))
  have hmap : (deningerFamilyDiagram S₀ sched).map (homOfLE (Nat.le_succ n)) =
      GrpCat.ofHom (deningerFamilyEmbed S₀ sched n) := by
    simp [deningerFamilyDiagram]
  rw [hmap] at h
  have h2 := congrArg (fun f : GrpCat.of ((deningerFamilyTower S₀ sched n).carrier) ⟶
    deningerFamilyColimit S₀ sched => f.hom x) h
  exact h2

/-- **The transition maps of the tower are injective.** -/
theorem deningerFamilyMap_injective (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerFamilyGood S₀) (n m : ℕ) (h : n ≤ m) :
    Function.Injective ((deningerFamilyDiagram S₀ sched).map (homOfLE h)).hom := by
  induction m, h using Nat.le_induction with
  | base =>
    intro x y hxy
    rw [Subsingleton.elim (homOfLE (le_refl n)) (𝟙 n),
      (deningerFamilyDiagram S₀ sched).map_id] at hxy
    exact hxy
  | succ m hm ih =>
    intro x y hxy
    have hcomp : (deningerFamilyDiagram S₀ sched).map (homOfLE (hm.trans (Nat.le_succ m))) =
        (deningerFamilyDiagram S₀ sched).map (homOfLE hm) ≫
          (deningerFamilyDiagram S₀ sched).map (homOfLE (Nat.le_succ m)) := by
      rw [← Functor.map_comp]
      congr 1
    rw [hcomp] at hxy
    refine ih ?_
    have hstep : ((deningerFamilyDiagram S₀ sched).map (homOfLE (Nat.le_succ m))).hom =
        deningerFamilyEmbed S₀ sched m := by
      show ((Functor.ofSequence
        (fun k => GrpCat.ofHom (deningerFamilyEmbed S₀ sched k))).map
          (homOfLE (Nat.le_succ m))).hom = _
      rw [Functor.ofSequence_map_homOfLE_succ]
      rfl
    have hxy' : (deningerFamilyEmbed S₀ sched m)
        (((deningerFamilyDiagram S₀ sched).map (homOfLE hm)).hom x) =
        (deningerFamilyEmbed S₀ sched m)
        (((deningerFamilyDiagram S₀ sched).map (homOfLE hm)).hom y) := by
      rw [← hstep]
      exact hxy
    exact deningerFamilyEmbed_injective S₀ sched hs h₀ m hxy'

/-- **The structure maps into the colimit are injective.** -/
theorem deningerFamilyIota_injective (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerFamilyGood S₀) (n : ℕ) :
    Function.Injective (deningerFamilyIota S₀ sched n) := by
  intro a b hab
  have h1 : Relation.EqvGen
      (Functor.ColimitTypeRel (deningerFamilyDiagram S₀ sched ⋙ forget GrpCat))
      ⟨n, a⟩ ⟨n, b⟩ := Quot.eq.mp hab
  have h2 : Limits.Types.FilteredColimit.Rel
      (deningerFamilyDiagram S₀ sched ⋙ forget GrpCat) ⟨n, a⟩ ⟨n, b⟩ := by
    rw [Limits.Types.FilteredColimit.rel_eq_eqvGen_colimitTypeRel]
    exact h1
  obtain ⟨k, f, g, hfg⟩ := h2
  have hle : n ≤ k := leOfHom f
  have hfg' : ((deningerFamilyDiagram S₀ sched).map (homOfLE hle)).hom a =
      ((deningerFamilyDiagram S₀ sched).map (homOfLE hle)).hom b := by
    rw [Subsingleton.elim (homOfLE hle) f, Subsingleton.elim f g]
    exact hfg
  exact deningerFamilyMap_injective S₀ sched hs h₀ n k hle hfg'

/-- **The colimit of the tower over a family has unique roots.** -/
theorem deningerFamilyColimit_uniqueRoots (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerFamilyGood S₀)
    (x y : deningerFamilyColimit S₀ sched) (k : ℕ) (hk : 0 < k) (h : x ^ k = y ^ k) : x = y :=
  deningerUniqueRoots_of_chain (fun n => deningerFamilyIota S₀ sched n)
    (fun n a => ⟨deningerFamilyEmbed S₀ sched n a, deningerFamilyIota_step S₀ sched n a⟩)
    (fun n => deningerFamilyIota_injective S₀ sched hs h₀ n)
    (fun z => deningerFamilyColimit_surjective S₀ sched z)
    (fun n a b j hj hab =>
      (deningerFamilyTower_good S₀ sched hs h₀ n).uniqueRoots a b j hj hab)
    x y k hk h

end RootAdjunction

end RHTower

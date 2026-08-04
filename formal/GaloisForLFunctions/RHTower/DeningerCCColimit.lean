import GaloisForLFunctions.RHTower.DeningerCCTower
import GaloisForLFunctions.RHTower.DeningerChainUniqueRoots
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The colimit of the tower of stages with cyclic centralizers

The chain of stages and embeddings is a functor out of the natural numbers, and its filtered colimit
is a group in which every element comes from a stage and no stage is collapsed.  Unique roots
transport to it from the stages.

* `deningerCCColimit` : the colimit.
* `deningerCCColimit_uniqueRoots` : it has unique roots.
-/

namespace RHTower

open CategoryTheory Monoid

universe u

namespace RootAdjunction

/-- The tower, as a functor. -/
noncomputable def deningerCCDiagram (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) :
    ℕ ⥤ GrpCat.{u} :=
  Functor.ofSequence (X := fun n => GrpCat.of ((deningerCCTower S₀ sched n).carrier))
    (fun n => GrpCat.ofHom (deningerCCEmbed S₀ sched n))

/-- **The colimit of the tower.** -/
noncomputable def deningerCCColimit (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) :
    GrpCat.{u} :=
  GrpCat.FilteredColimits.colimit (deningerCCDiagram S₀ sched)

/-- The structure map of a stage into the colimit. -/
noncomputable def deningerCCIota (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) (n : ℕ) :
    (deningerCCTower S₀ sched n).carrier →* (deningerCCColimit S₀ sched) :=
  ((GrpCat.FilteredColimits.colimitCocone (deningerCCDiagram S₀ sched)).ι.app n).hom

/-- **Every element of the colimit comes from a stage.** -/
theorem deningerCCColimit_surjective (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (x : deningerCCColimit S₀ sched) :
    ∃ (n : ℕ) (a : (deningerCCTower S₀ sched n).carrier),
      deningerCCIota S₀ sched n a = x := by
  refine Quot.inductionOn x ?_
  rintro ⟨n, a⟩
  exact ⟨n, a, rfl⟩

/-- **The structure maps are compatible with the embeddings.** -/
theorem deningerCCIota_step (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) (n : ℕ)
    (x : (deningerCCTower S₀ sched n).carrier) :
    deningerCCIota S₀ sched (n + 1) (deningerCCEmbed S₀ sched n x) =
      deningerCCIota S₀ sched n x := by
  have h := (GrpCat.FilteredColimits.colimitCocone (deningerCCDiagram S₀ sched)).w
    (homOfLE (Nat.le_succ n))
  have hmap : (deningerCCDiagram S₀ sched).map (homOfLE (Nat.le_succ n)) =
      GrpCat.ofHom (deningerCCEmbed S₀ sched n) := by
    simp [deningerCCDiagram]
  rw [hmap] at h
  have h2 := congrArg (fun f : GrpCat.of ((deningerCCTower S₀ sched n).carrier) ⟶
    deningerCCColimit S₀ sched => f.hom x) h
  exact h2

/-- **The transition maps of the tower are injective.** -/
theorem deningerCCMap_injective (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerCCGood S₀) (n m : ℕ) (h : n ≤ m) :
    Function.Injective ((deningerCCDiagram S₀ sched).map (homOfLE h)).hom := by
  induction m, h using Nat.le_induction with
  | base =>
    intro x y hxy
    rw [Subsingleton.elim (homOfLE (le_refl n)) (𝟙 n),
      (deningerCCDiagram S₀ sched).map_id] at hxy
    exact hxy
  | succ m hm ih =>
    intro x y hxy
    have hcomp : (deningerCCDiagram S₀ sched).map (homOfLE (hm.trans (Nat.le_succ m))) =
        (deningerCCDiagram S₀ sched).map (homOfLE hm) ≫
          (deningerCCDiagram S₀ sched).map (homOfLE (Nat.le_succ m)) := by
      rw [← Functor.map_comp]
      congr 1
    rw [hcomp] at hxy
    refine ih ?_
    have hstep : ((deningerCCDiagram S₀ sched).map (homOfLE (Nat.le_succ m))).hom =
        deningerCCEmbed S₀ sched m := by
      show ((Functor.ofSequence
        (fun k => GrpCat.ofHom (deningerCCEmbed S₀ sched k))).map
          (homOfLE (Nat.le_succ m))).hom = _
      rw [Functor.ofSequence_map_homOfLE_succ]
      rfl
    have hxy' : (deningerCCEmbed S₀ sched m)
        (((deningerCCDiagram S₀ sched).map (homOfLE hm)).hom x) =
        (deningerCCEmbed S₀ sched m)
        (((deningerCCDiagram S₀ sched).map (homOfLE hm)).hom y) := by
      rw [← hstep]
      exact hxy
    exact deningerCCEmbed_injective S₀ sched hs h₀ m hxy'

/-- **The structure maps into the colimit are injective.** -/
theorem deningerCCIota_injective (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerCCGood S₀) (n : ℕ) :
    Function.Injective (deningerCCIota S₀ sched n) := by
  intro a b hab
  have h1 : Relation.EqvGen
      (Functor.ColimitTypeRel (deningerCCDiagram S₀ sched ⋙ forget GrpCat))
      ⟨n, a⟩ ⟨n, b⟩ := Quot.eq.mp hab
  have h2 : Limits.Types.FilteredColimit.Rel
      (deningerCCDiagram S₀ sched ⋙ forget GrpCat) ⟨n, a⟩ ⟨n, b⟩ := by
    rw [Limits.Types.FilteredColimit.rel_eq_eqvGen_colimitTypeRel]
    exact h1
  obtain ⟨k, f, g, hfg⟩ := h2
  have hle : n ≤ k := leOfHom f
  have hfg' : ((deningerCCDiagram S₀ sched).map (homOfLE hle)).hom a =
      ((deningerCCDiagram S₀ sched).map (homOfLE hle)).hom b := by
    rw [Subsingleton.elim (homOfLE hle) f, Subsingleton.elim f g]
    exact hfg
  exact deningerCCMap_injective S₀ sched hs h₀ n k hle hfg'

/-- **The colimit of the tower has unique roots.** -/
theorem deningerCCColimit_uniqueRoots (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerCCGood S₀)
    (x y : deningerCCColimit S₀ sched) (k : ℕ) (hk : 0 < k) (h : x ^ k = y ^ k) : x = y :=
  deningerUniqueRoots_of_chain (fun n => deningerCCIota S₀ sched n)
    (fun n a => ⟨deningerCCEmbed S₀ sched n a, deningerCCIota_step S₀ sched n a⟩)
    (fun n => deningerCCIota_injective S₀ sched hs h₀ n)
    (fun z => deningerCCColimit_surjective S₀ sched z)
    (fun n a b j hj hab =>
      (deningerCCTower_good S₀ sched hs h₀ n).uniqueRoots a b j hj hab)
    x y k hk h

end RootAdjunction

end RHTower

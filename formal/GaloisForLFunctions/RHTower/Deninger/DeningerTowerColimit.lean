import GaloisForLFunctions.RHTower.Deninger.DeningerChainUniqueRoots
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The colimit of the tower

The tower of root adjunctions is a sequence of groups and injections, hence a functor out of the
natural numbers, and the natural numbers are filtered, so the colimit of that functor is a group.
Every element of the colimit comes from a stage, since the underlying type is a quotient of the
disjoint union of the stages.

* `deningerTowerDiagram` : the tower as a functor.
* `deningerTowerColimit` : its colimit.
* `deningerTowerColimit_surjective` : every element comes from a stage.
* `deningerTowerIota_step` : the structure maps are compatible.
-/

namespace RHTower

open CategoryTheory Monoid

universe u

namespace RootAdjunction

/-- **The tower as a functor out of the natural numbers.** -/
noncomputable def deningerTowerDiagram (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) :
    ℕ ⥤ GrpCat.{u} :=
  Functor.ofSequence (X := fun n => GrpCat.of ((deningerRootTower S₀ ms n).carrier))
    (fun n => GrpCat.ofHom (deningerTowerEmbed S₀ ms n))

/-- **The colimit of the tower.** -/
noncomputable def deningerTowerColimit (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) : GrpCat.{u} :=
  GrpCat.FilteredColimits.colimit (deningerTowerDiagram S₀ ms)

/-- The structure map of a stage into the colimit. -/
noncomputable def deningerTowerIota (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) (n : ℕ) :
    (deningerRootTower S₀ ms n).carrier →* (deningerTowerColimit S₀ ms) :=
  ((GrpCat.FilteredColimits.colimitCocone (deningerTowerDiagram S₀ ms)).ι.app n).hom

/-- **Every element of the colimit comes from a stage.** -/
theorem deningerTowerColimit_surjective (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ)
    (x : deningerTowerColimit S₀ ms) :
    ∃ (n : ℕ) (a : (deningerRootTower S₀ ms n).carrier), deningerTowerIota S₀ ms n a = x := by
  refine Quot.inductionOn x ?_
  rintro ⟨n, a⟩
  exact ⟨n, a, rfl⟩

/-- **The structure maps are compatible with the embeddings.** -/
theorem deningerTowerIota_step (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) (n : ℕ)
    (x : (deningerRootTower S₀ ms n).carrier) :
    deningerTowerIota S₀ ms (n + 1) (deningerTowerEmbed S₀ ms n x) =
      deningerTowerIota S₀ ms n x := by
  have h := (GrpCat.FilteredColimits.colimitCocone (deningerTowerDiagram S₀ ms)).w
    (homOfLE (Nat.le_succ n))
  have hmap : (deningerTowerDiagram S₀ ms).map (homOfLE (Nat.le_succ n)) =
      GrpCat.ofHom (deningerTowerEmbed S₀ ms n) := by
    simp [deningerTowerDiagram]
  rw [hmap] at h
  have h2 := congrArg (fun f : GrpCat.of ((deningerRootTower S₀ ms n).carrier) ⟶
    deningerTowerColimit S₀ ms => f.hom x) h
  exact h2

end RootAdjunction

end RHTower

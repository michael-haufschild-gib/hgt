import GaloisForLFunctions.RHTower.DeningerTowerColimit

/-!
# The transition maps of the tower are injective

The map of the tower's diagram attached to an inequality is a composite of the embeddings between
consecutive stages, each of which is injective, so it is injective.  This is what identifies two
elements of a stage which become equal further up.

* `deningerTowerMap_injective` : the transition maps are injective.
-/

namespace RHTower

open CategoryTheory Monoid

universe u

namespace RootAdjunction

/-- **The transition maps of the tower are injective.** -/
theorem deningerTowerMap_injective (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ)
    (hms : ∀ n, 2 ≤ (ms n).natAbs) (h₀ : DeningerGoodStage S₀) (n m : ℕ) (h : n ≤ m) :
    Function.Injective ((deningerTowerDiagram S₀ ms).map (homOfLE h)).hom := by
  induction m, h using Nat.le_induction with
  | base =>
    intro x y hxy
    rw [Subsingleton.elim (homOfLE (le_refl n)) (𝟙 n), (deningerTowerDiagram S₀ ms).map_id]
      at hxy
    exact hxy
  | succ m hm ih =>
    intro x y hxy
    have hcomp : (deningerTowerDiagram S₀ ms).map (homOfLE (hm.trans (Nat.le_succ m))) =
        (deningerTowerDiagram S₀ ms).map (homOfLE hm) ≫
          (deningerTowerDiagram S₀ ms).map (homOfLE (Nat.le_succ m)) := by
      rw [← Functor.map_comp]
      congr 1
    rw [hcomp] at hxy
    refine ih ?_
    have hstep : ((deningerTowerDiagram S₀ ms).map (homOfLE (Nat.le_succ m))).hom =
        deningerTowerEmbed S₀ ms m := by
      show ((Functor.ofSequence
        (fun k => GrpCat.ofHom (deningerTowerEmbed S₀ ms k))).map
          (homOfLE (Nat.le_succ m))).hom = _
      rw [Functor.ofSequence_map_homOfLE_succ]
      rfl
    have hxy' : (deningerTowerEmbed S₀ ms m)
        (((deningerTowerDiagram S₀ ms).map (homOfLE hm)).hom x) =
        (deningerTowerEmbed S₀ ms m)
        (((deningerTowerDiagram S₀ ms).map (homOfLE hm)).hom y) := by
      rw [← hstep]
      exact hxy
    exact deningerTowerEmbed_injective S₀ ms hms h₀ m hxy'

end RootAdjunction

end RHTower

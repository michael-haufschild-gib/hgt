import GaloisForLFunctions.RHTower.Deninger.DeningerTowerMapInj
import GaloisForLFunctions.RHTower.Deninger.DeningerChainUniqueRoots

/-!
# The structure maps into the colimit are injective

Two elements of a stage with the same image in the colimit are identified at some later stage, by
the explicit description of the equivalence relation defining a filtered colimit of types.  The
transition maps of the tower are injective, so no later stage identifies them.

* `deningerTowerIota_injective` : the structure maps are injective.
* `deningerTowerColimit_uniqueRoots` : the colimit has unique roots.
-/

namespace RHTower

open CategoryTheory Monoid

universe u

namespace RootAdjunction

/-- **The structure maps into the colimit are injective.** -/
theorem deningerTowerIota_injective (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ)
    (hms : ∀ n, 2 ≤ (ms n).natAbs) (h₀ : DeningerGoodStage S₀) (n : ℕ) :
    Function.Injective (deningerTowerIota S₀ ms n) := by
  intro a b hab
  have h1 : Relation.EqvGen
      (Functor.ColimitTypeRel (deningerTowerDiagram S₀ ms ⋙ forget GrpCat))
      ⟨n, a⟩ ⟨n, b⟩ := Quot.eq.mp hab
  have h2 : Limits.Types.FilteredColimit.Rel
      (deningerTowerDiagram S₀ ms ⋙ forget GrpCat) ⟨n, a⟩ ⟨n, b⟩ := by
    rw [Limits.Types.FilteredColimit.rel_eq_eqvGen_colimitTypeRel]
    exact h1
  obtain ⟨k, f, g, hfg⟩ := h2
  have hle : n ≤ k := leOfHom f
  have hfg' : ((deningerTowerDiagram S₀ ms).map (homOfLE hle)).hom a =
      ((deningerTowerDiagram S₀ ms).map (homOfLE hle)).hom b := by
    rw [Subsingleton.elim (homOfLE hle) f, Subsingleton.elim f g]
    exact hfg
  exact deningerTowerMap_injective S₀ ms hms h₀ n k hle hfg'

/-- **The colimit of the tower has unique roots.** -/
theorem deningerTowerColimit_uniqueRoots (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ)
    (hms : ∀ n, 2 ≤ (ms n).natAbs) (h₀ : DeningerGoodStage S₀)
    (x y : deningerTowerColimit S₀ ms) (k : ℕ) (hk : 0 < k) (h : x ^ k = y ^ k) : x = y :=
  deningerUniqueRoots_of_chain (fun n => deningerTowerIota S₀ ms n)
    (fun n a => ⟨deningerTowerEmbed S₀ ms n a, deningerTowerIota_step S₀ ms n a⟩)
    (fun n => deningerTowerIota_injective S₀ ms hms h₀ n)
    (fun z => deningerTowerColimit_surjective S₀ ms z)
    (fun n a b j hj hab => (deningerRootTower_good S₀ ms hms h₀ n).uniqueRoots a b j hj hab)
    x y k hk h

end RootAdjunction

end RHTower

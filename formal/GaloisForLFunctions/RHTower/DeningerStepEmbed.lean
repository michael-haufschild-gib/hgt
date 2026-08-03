import GaloisForLFunctions.RHTower.DeningerRootTowerGood

/-!
# The stages of the tower embed in one another

A stage embeds in the next one as the group factor of the amalgam, and the distinguished element of
the next stage is an `m`-th root of the image of the distinguished element of this one.  So the
tower is an increasing chain in which the chosen element acquires the chosen root at every step.

* `deningerStepEmbed` : the embedding of a stage in the next.
* `deningerStepEmbed_injective` : it is injective.
* `deningerStepEmbed_root` : the new distinguished element is a root of the old one.
* `deningerTowerEmbed` : the embeddings along the tower.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- **The embedding of a stage in the next**, as the group factor of the amalgam. -/
noncomputable def deningerStepEmbed (S : DeningerRootStage.{u}) (m : ℤ) :
    S.carrier →* (deningerRootStep S m).carrier :=
  PushoutI.of (φ := deningerRootMap S.carrier S.elt m) (ULift.up true)

/-- **The embedding is injective.** -/
theorem deningerStepEmbed_injective (S : DeningerRootStage.{u}) (m : ℤ) (hm : m ≠ 0)
    (hord : ∀ n : ℤ, S.elt ^ n = 1 → n = 0) :
    Function.Injective (deningerStepEmbed S m) :=
  PushoutI.of_injective (deningerRootMap_injective S.carrier S.elt m hm hord) (ULift.up true)

/-- **The new distinguished element is an `m`-th root of the image of the old one.** -/
theorem deningerStepEmbed_root (S : DeningerRootStage.{u}) (m : ℤ) :
    (deningerRootStep S m).elt ^ m = deningerStepEmbed S m S.elt :=
  deningerRootElt_zpow S.carrier S.elt m

/-- **The embeddings along the tower.** -/
noncomputable def deningerTowerEmbed (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) (n : ℕ) :
    (deningerRootTower S₀ ms n).carrier →* (deningerRootTower S₀ ms (n + 1)).carrier :=
  deningerStepEmbed (deningerRootTower S₀ ms n) (ms n)

/-- **The embeddings along the tower are injective.** -/
theorem deningerTowerEmbed_injective (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ)
    (hms : ∀ n, 2 ≤ (ms n).natAbs) (h₀ : DeningerGoodStage S₀) (n : ℕ) :
    Function.Injective (deningerTowerEmbed S₀ ms n) :=
  deningerStepEmbed_injective _ _ (by have := hms n; omega)
    (deningerRootTower_good S₀ ms hms h₀ n).order

/-- **Along the tower the distinguished element acquires the chosen root.** -/
theorem deningerTowerEmbed_root (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) (n : ℕ) :
    (deningerRootTower S₀ ms (n + 1)).elt ^ (ms n) =
      deningerTowerEmbed S₀ ms n (deningerRootTower S₀ ms n).elt :=
  deningerStepEmbed_root (deningerRootTower S₀ ms n) (ms n)

end RootAdjunction

end RHTower

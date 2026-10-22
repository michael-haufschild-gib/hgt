import GaloisForLFunctions.RHTower.Deninger.DeningerTowerIotaInj

/-!
# Roots in the colimit of the tower

The image of the distinguished element of a stage is the chosen power of the image of the
distinguished element of the next stage, so along the tower the image of the starting element
acquires all the chosen roots.  Torsion freeness of the colimit is a special case of unique roots.

* `deningerTowerColimit_root` : the coherent system of roots.
* `deningerTowerColimit_torsionFree` : the colimit is torsion free.
-/

namespace RHTower

open CategoryTheory Monoid

universe u

namespace RootAdjunction

/-- **The images of the distinguished elements form a coherent system of roots.** -/
theorem deningerTowerColimit_root (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) (n : ℕ) :
    (deningerTowerIota S₀ ms (n + 1) (deningerRootTower S₀ ms (n + 1)).elt) ^ (ms n) =
      deningerTowerIota S₀ ms n (deningerRootTower S₀ ms n).elt := by
  rw [← map_zpow, deningerTowerEmbed_root, deningerTowerIota_step]

/-- **The colimit of the tower is torsion free.** -/
theorem deningerTowerColimit_torsionFree (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ)
    (hms : ∀ n, 2 ≤ (ms n).natAbs) (h₀ : DeningerGoodStage S₀)
    (x : deningerTowerColimit S₀ ms) (k : ℕ) (hk : 0 < k) (h : x ^ k = 1) : x = 1 := by
  refine deningerTowerColimit_uniqueRoots S₀ ms hms h₀ x 1 k hk ?_
  rw [one_pow]
  exact h

end RootAdjunction

end RHTower

import GaloisForLFunctions.RHTower.DeningerTowerColimitRoot
import GaloisForLFunctions.RHTower.DeningerRootTwo
import GaloisForLFunctions.RHTower.DeningerAmalgamCyclic

/-!
# Homology along the tower

Each step of the tower is a root adjunction, which preserves the vanishing of homology in degree two
and in every degree at least three.  So the vanishing passes up the whole tower.

* `deningerRootTower_isZero_two` : degree two along the tower.
* `deningerRootTower_isZero` : degrees at least three along the tower.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits Monoid

universe u

namespace RootAdjunction

/-- **Degree two along the tower.** -/
theorem deningerRootTower_isZero_two (k : Type u) [Field k] [CharZero k]
    (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) (hms : ∀ n, 2 ≤ (ms n).natAbs)
    (h₀ : DeningerGoodStage S₀)
    (hz : IsZero (groupHomology (Rep.trivial k S₀.carrier k) 2)) (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k (deningerRootTower S₀ ms n).carrier k) 2) := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    have hgood := deningerRootTower_good S₀ ms hms h₀ n
    exact deningerRootAdjunction_isZero_two (deningerRootTower S₀ ms n).carrier
      (deningerRootTower S₀ ms n).elt (ms n) (by have := hms n; omega) hgood.order k ih

/-- **Degrees at least three along the tower.** -/
theorem deningerRootTower_isZero (k : Type u) [CommRing k]
    (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) (hms : ∀ n, 2 ≤ (ms n).natAbs)
    (h₀ : DeningerGoodStage S₀) (j : ℕ)
    (hz : IsZero (groupHomology (Rep.trivial k S₀.carrier k) (j + 3))) (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k (deningerRootTower S₀ ms n).carrier k) (j + 3)) := by
  classical
  induction n with
  | zero => exact hz
  | succ n ih =>
    have hgood := deningerRootTower_good S₀ ms hms h₀ n
    exact deningerRootAdjunction_isZero (deningerRootTower S₀ ms n).carrier
      (deningerRootTower S₀ ms n).elt (ms n) (by have := hms n; omega) hgood.order k j ih

end RootAdjunction

end RHTower

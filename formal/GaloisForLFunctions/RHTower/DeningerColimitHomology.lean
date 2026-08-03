import GaloisForLFunctions.RHTower.DeningerRootTowerHomology
import GaloisForLFunctions.RHTower.DeningerHomologyUnion

/-!
# Homology of the colimit of the tower

The images of the stages are an increasing chain of subgroups of the colimit whose union is
everything, and each is isomorphic to its stage, so the vanishing of homology along the tower passes
to the colimit.

* `deningerTowerColimit_isZero` : vanishing in the colimit.
* `deningerTowerColimit_isZero_two` : the case of degree two.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits Monoid

universe u

namespace RootAdjunction

/-- **Vanishing of homology passes to the colimit.** -/
theorem deningerTowerColimit_isZero (k : Type u) [CommRing k]
    (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) (hms : ∀ n, 2 ≤ (ms n).natAbs)
    (h₀ : DeningerGoodStage S₀) (j : ℕ)
    (hstage : ∀ n, IsZero
      (groupHomology (Rep.trivial k (deningerRootTower S₀ ms n).carrier k) (j + 1))) :
    IsZero (groupHomology (Rep.trivial k (deningerTowerColimit S₀ ms) k) (j + 1)) := by
  classical
  refine deningerIsZero_of_iUnion k ↥(deningerTowerColimit S₀ ms)
    (fun n => (deningerTowerIota S₀ ms n).range) ?_ ?_ j ?_
  · refine monotone_nat_of_le_succ (fun n => ?_)
    rintro x ⟨a, rfl⟩
    exact ⟨deningerTowerEmbed S₀ ms n a, deningerTowerIota_step S₀ ms n a⟩
  · intro g
    obtain ⟨n, a, ha⟩ := deningerTowerColimit_surjective S₀ ms g
    exact ⟨n, a, ha⟩
  · intro n
    refine IsZero.of_iso (hstage n) ?_
    exact deningerTrivialHomologyIso
      (MonoidHom.ofInjective (deningerTowerIota_injective S₀ ms hms h₀ n)).symm k (j + 1)

/-- **The case of degree two**, from the infinite cyclic starting stage. -/
theorem deningerTowerColimit_isZero_two (k : Type u) [Field k] [CharZero k]
    (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) (hms : ∀ n, 2 ≤ (ms n).natAbs)
    (h₀ : DeningerGoodStage S₀)
    (hz : IsZero (groupHomology (Rep.trivial k S₀.carrier k) 2)) :
    IsZero (groupHomology (Rep.trivial k (deningerTowerColimit S₀ ms) k) 2) :=
  deningerTowerColimit_isZero k S₀ ms hms h₀ 1
    (fun n => deningerRootTower_isZero_two k S₀ ms hms h₀ hz n)

end RootAdjunction

end RHTower

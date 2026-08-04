import GaloisForLFunctions.RHTower.DeningerFamilyColimit
import GaloisForLFunctions.RHTower.DeningerRootTowerHomology
import GaloisForLFunctions.RHTower.DeningerHomologyUnion

/-!
# Homology along the tower over a family

Each step is a root adjunction, so the vanishing of homology in degree two and in every degree at
least three passes up the tower, and from the stages to the colimit by the union argument.

* `deningerFamilyTower_isZero_two`, `deningerFamilyTower_isZero` : along the tower.
* `deningerFamilyColimit_isZero` : in the colimit.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits Monoid

universe u

namespace RootAdjunction

/-- **Degree two along the tower over a family.** -/
theorem deningerFamilyTower_isZero_two (k : Type u) [Field k] [CharZero k]
    (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) (hs : ∀ n, 2 ≤ (sched n).2.natAbs)
    (h₀ : DeningerFamilyGood S₀)
    (hz : IsZero (groupHomology (Rep.trivial k S₀.carrier k) 2)) (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k (deningerFamilyTower S₀ sched n).carrier k) 2) := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    have hgood := deningerFamilyTower_good S₀ sched hs h₀ n
    exact deningerRootAdjunction_isZero_two (deningerFamilyTower S₀ sched n).carrier
      ((deningerFamilyTower S₀ sched n).fam (sched n).1) (sched n).2
      (by have := hs n; omega) (hgood.order (sched n).1) k ih

/-- **Degrees at least three along the tower over a family.** -/
theorem deningerFamilyTower_isZero (k : Type u) [CommRing k]
    (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) (hs : ∀ n, 2 ≤ (sched n).2.natAbs)
    (h₀ : DeningerFamilyGood S₀) (j : ℕ)
    (hz : IsZero (groupHomology (Rep.trivial k S₀.carrier k) (j + 3))) (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k (deningerFamilyTower S₀ sched n).carrier k) (j + 3)) := by
  classical
  induction n with
  | zero => exact hz
  | succ n ih =>
    have hgood := deningerFamilyTower_good S₀ sched hs h₀ n
    exact deningerRootAdjunction_isZero (deningerFamilyTower S₀ sched n).carrier
      ((deningerFamilyTower S₀ sched n).fam (sched n).1) (sched n).2
      (by have := hs n; omega) (hgood.order (sched n).1) k j ih

/-- **Vanishing of homology passes to the colimit.** -/
theorem deningerFamilyColimit_isZero (k : Type u) [CommRing k]
    (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) (hs : ∀ n, 2 ≤ (sched n).2.natAbs)
    (h₀ : DeningerFamilyGood S₀) (j : ℕ)
    (hstage : ∀ n, IsZero
      (groupHomology (Rep.trivial k (deningerFamilyTower S₀ sched n).carrier k) (j + 1))) :
    IsZero (groupHomology (Rep.trivial k (deningerFamilyColimit S₀ sched) k) (j + 1)) := by
  classical
  refine deningerIsZero_of_iUnion k ↥(deningerFamilyColimit S₀ sched)
    (fun n => (deningerFamilyIota S₀ sched n).range) ?_ ?_ j ?_
  · refine monotone_nat_of_le_succ (fun n => ?_)
    rintro x ⟨a, rfl⟩
    exact ⟨deningerFamilyEmbed S₀ sched n a, deningerFamilyIota_step S₀ sched n a⟩
  · intro g
    obtain ⟨n, a, ha⟩ := deningerFamilyColimit_surjective S₀ sched g
    exact ⟨n, a, ha⟩
  · intro n
    refine IsZero.of_iso (hstage n) ?_
    exact deningerTrivialHomologyIso
      (MonoidHom.ofInjective (deningerFamilyIota_injective S₀ sched hs h₀ n)).symm k (j + 1)

end RootAdjunction

end RHTower

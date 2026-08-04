import GaloisForLFunctions.RHTower.DeningerCCColimit
import GaloisForLFunctions.RHTower.DeningerRootTowerHomology
import GaloisForLFunctions.RHTower.DeningerHomologyUnion

/-!
# Homology along the tower of stages with cyclic centralizers

Each step is a root adjunction, so the vanishing of homology in degree two and in every degree at
least three passes up the tower, and from the stages to the colimit by the union argument.

* `deningerCCTower_isZero_two`, `deningerCCTower_isZero` : along the tower.
* `deningerCCColimit_isZero` : in the colimit.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits Monoid

universe u

namespace RootAdjunction

/-- **Degree two along the tower.** -/
theorem deningerCCTower_isZero_two (k : Type u) [Field k] [CharZero k]
    (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) (hs : ∀ n, 2 ≤ (sched n).2.natAbs)
    (h₀ : DeningerCCGood S₀)
    (hz : IsZero (groupHomology (Rep.trivial k S₀.carrier k) 2)) (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k (deningerCCTower S₀ sched n).carrier k) 2) := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    have hgood := deningerCCTower_good S₀ sched hs h₀ n
    exact deningerRootAdjunction_isZero_two (deningerCCTower S₀ sched n).carrier
      (deningerCCRoot (deningerCCTower S₀ sched n) (sched n).1) (sched n).2
      (by have := hs n; omega)
      (deningerCCRoot_order (deningerCCTower S₀ sched n) hgood (sched n).1) k ih

/-- **Degrees at least three along the tower.** -/
theorem deningerCCTower_isZero (k : Type u) [CommRing k]
    (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) (hs : ∀ n, 2 ≤ (sched n).2.natAbs)
    (h₀ : DeningerCCGood S₀) (j : ℕ)
    (hz : IsZero (groupHomology (Rep.trivial k S₀.carrier k) (j + 3))) (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k (deningerCCTower S₀ sched n).carrier k) (j + 3)) := by
  classical
  induction n with
  | zero => exact hz
  | succ n ih =>
    have hgood := deningerCCTower_good S₀ sched hs h₀ n
    exact deningerRootAdjunction_isZero (deningerCCTower S₀ sched n).carrier
      (deningerCCRoot (deningerCCTower S₀ sched n) (sched n).1) (sched n).2
      (by have := hs n; omega)
      (deningerCCRoot_order (deningerCCTower S₀ sched n) hgood (sched n).1) k j ih

/-- **Vanishing of homology passes to the colimit.** -/
theorem deningerCCColimit_isZero (k : Type u) [CommRing k]
    (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) (hs : ∀ n, 2 ≤ (sched n).2.natAbs)
    (h₀ : DeningerCCGood S₀) (j : ℕ)
    (hstage : ∀ n, IsZero
      (groupHomology (Rep.trivial k (deningerCCTower S₀ sched n).carrier k) (j + 1))) :
    IsZero (groupHomology (Rep.trivial k (deningerCCColimit S₀ sched) k) (j + 1)) := by
  classical
  refine deningerIsZero_of_iUnion k ↥(deningerCCColimit S₀ sched)
    (fun n => (deningerCCIota S₀ sched n).range) ?_ ?_ j ?_
  · refine monotone_nat_of_le_succ (fun n => ?_)
    rintro x ⟨a, rfl⟩
    exact ⟨deningerCCEmbed S₀ sched n a, deningerCCIota_step S₀ sched n a⟩
  · intro g
    obtain ⟨n, a, ha⟩ := deningerCCColimit_surjective S₀ sched g
    exact ⟨n, a, ha⟩
  · intro n
    refine IsZero.of_iso (hstage n) ?_
    exact deningerTrivialHomologyIso
      (MonoidHom.ofInjective (deningerCCIota_injective S₀ sched hs h₀ n)).symm k (j + 1)

end RootAdjunction

end RHTower

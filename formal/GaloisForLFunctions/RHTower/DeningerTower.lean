import GaloisForLFunctions.RHTower.DeningerRootElement
import GaloisForLFunctions.RHTower.DeningerRootTorsionFree

/-!
# A tower of root adjunctions

Iterating the root adjunction gives a tower of groups, each obtained from the previous by adjoining
one root.  Torsion freeness and the vanishing of homology in degrees at least two pass along the
whole tower, whatever roots are chosen.

* `DeningerStage`, `deningerTower` : the tower.
* `deningerTower_torsionFree` : every stage is torsion free.
* `deningerTower_isZero_two` : every stage has vanishing second homology.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory CategoryTheory.Limits

universe u

namespace RootAdjunction

/-- A stage of a tower of root adjunctions. -/
structure DeningerStage : Type (u + 1) where
  /-- The underlying group of the stage. -/
  carrier : Type u
  /-- Its group structure. -/
  [group : Group carrier]

attribute [instance] DeningerStage.group

/-- Adjoining a root to a stage. -/
noncomputable def deningerStep (S : DeningerStage.{u}) (a : S.carrier) (m : ℤ) :
    DeningerStage.{u} :=
  ⟨PushoutI (deningerRootMap S.carrier a m)⟩

/-- **The tower of root adjunctions** attached to a choice of element and exponent at each stage. -/
noncomputable def deningerTower (S₀ : DeningerStage.{u})
    (d : ∀ S : DeningerStage.{u}, S.carrier × ℤ) : ℕ → DeningerStage.{u}
  | 0 => S₀
  | n + 1 => deningerStep (deningerTower S₀ d n) (d (deningerTower S₀ d n)).1
      (d (deningerTower S₀ d n)).2

/-- The chosen element of a stage has infinite order, provided the stage is torsion free and the
element is not trivial. -/
theorem deningerInfiniteOrder {X : Type u} [Group X] (x : X) (hx : x ≠ 1)
    (htf : ∀ (y : X) (n : ℕ), 0 < n → y ^ n = 1 → y = 1) (n : ℤ) (hn : x ^ n = 1) : n = 0 := by
  by_contra hne
  refine hx (htf x n.natAbs (Int.natAbs_pos.2 hne) ?_)
  have hkey : x ^ ((n.natAbs : ℤ)) = 1 := by
    rcases Int.natAbs_eq n with h | h
    · rw [← h]; exact hn
    · rw [show ((n.natAbs : ℤ)) = -n by omega, zpow_neg, hn, inv_one]
  rwa [zpow_natCast] at hkey

variable (S₀ : DeningerStage.{u}) (d : ∀ S : DeningerStage.{u}, S.carrier × ℤ)

/-- **Every stage of the tower is torsion free.** -/
theorem deningerTower_torsionFree
    (h0 : ∀ (y : S₀.carrier) (n : ℕ), 0 < n → y ^ n = 1 → y = 1)
    (hm : ∀ S, (d S).2 ≠ 0) (hne : ∀ S, (d S).1 ≠ 1) (n : ℕ) :
    ∀ (y : (deningerTower S₀ d n).carrier) (j : ℕ), 0 < j → y ^ j = 1 → y = 1 := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    exact deningerRootAdjunction_torsionFree _ _ _ (hm _)
      (deningerInfiniteOrder _ (hne _) ih) ih

/-- **Every stage of the tower has vanishing second homology.** -/
theorem deningerTower_isZero_two (k : Type u) [Field k] [CharZero k]
    (h0 : ∀ (y : S₀.carrier) (n : ℕ), 0 < n → y ^ n = 1 → y = 1)
    (hm : ∀ S, (d S).2 ≠ 0) (hne : ∀ S, (d S).1 ≠ 1)
    (hz : IsZero (groupHomology (Rep.trivial k S₀.carrier k) 2)) (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k (deningerTower S₀ d n).carrier k) 2) := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    exact deningerRootAdjunction_isZero_two _ _ _ (hm _)
      (deningerInfiniteOrder _ (hne _) (deningerTower_torsionFree S₀ d h0 hm hne n)) k ih

end RootAdjunction

end RHTower

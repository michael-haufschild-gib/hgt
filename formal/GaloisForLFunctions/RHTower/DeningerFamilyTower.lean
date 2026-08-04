import GaloisForLFunctions.RHTower.DeningerFamilyStage

/-!
# The tower over a family

Iterating the step along a schedule — which member to root and with which exponent at each stage —
preserves the invariant, and the stages embed in one another as the group factors of the amalgams.

* `deningerFamilyTower` : the tower.
* `deningerFamilyTower_good` : every stage satisfies the invariant.
* `deningerFamilyEmbed` : the embeddings, and their injectivity.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- **The tower over a family**, along a schedule of members and exponents. -/
noncomputable def deningerFamilyTower (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) :
    ℕ → DeningerFamilyStage.{u}
  | 0 => S₀
  | n + 1 => deningerFamilyStep (deningerFamilyTower S₀ sched n) (sched n).1 (sched n).2

/-- **Every stage of the tower satisfies the invariant.** -/
theorem deningerFamilyTower_good (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerFamilyGood S₀) (n : ℕ) :
    DeningerFamilyGood (deningerFamilyTower S₀ sched n) := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    exact deningerFamilyStep_good (deningerFamilyTower S₀ sched n) (sched n).1 (sched n).2
      (hs n) ih

/-- **The embeddings along the tower.** -/
noncomputable def deningerFamilyEmbed (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) (n : ℕ) :
    (deningerFamilyTower S₀ sched n).carrier →*
      (deningerFamilyTower S₀ sched (n + 1)).carrier :=
  PushoutI.of (φ := deningerRootMap (deningerFamilyTower S₀ sched n).carrier
    ((deningerFamilyTower S₀ sched n).fam (sched n).1) (sched n).2) (ULift.up true)

/-- **The embeddings along the tower are injective.** -/
theorem deningerFamilyEmbed_injective (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerFamilyGood S₀) (n : ℕ) :
    Function.Injective (deningerFamilyEmbed S₀ sched n) :=
  PushoutI.of_injective
    (deningerRootMap_injective (deningerFamilyTower S₀ sched n).carrier
      ((deningerFamilyTower S₀ sched n).fam (sched n).1) (sched n).2
      (by have := hs n; omega)
      ((deningerFamilyTower_good S₀ sched hs h₀ n).order (sched n).1))
    (ULift.up true)

end RootAdjunction

end RHTower

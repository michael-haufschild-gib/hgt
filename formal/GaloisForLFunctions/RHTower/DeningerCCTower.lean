import GaloisForLFunctions.RHTower.DeningerCCStage

/-!
# The tower of stages with cyclic centralizers

Iterating the step along a schedule — which enumerated element to root and with which exponent at
each stage — preserves the invariant, and the stages embed in one another as the group factors of
the amalgams.

* `deningerCCTower` : the tower.
* `deningerCCTower_good` : every stage satisfies the invariant.
* `deningerCCEmbed` : the embeddings, and their injectivity.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- **The tower**, along a schedule of enumeration indices and exponents. -/
noncomputable def deningerCCTower (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) :
    ℕ → DeningerCCStage.{u}
  | 0 => S₀
  | n + 1 => deningerCCStep (deningerCCTower S₀ sched n) n (sched n).1 (sched n).2

/-- **Every stage of the tower satisfies the invariant.** -/
theorem deningerCCTower_good (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerCCGood S₀) (n : ℕ) :
    DeningerCCGood (deningerCCTower S₀ sched n) := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    exact deningerCCStep_good (deningerCCTower S₀ sched n) ih n (sched n).1 (sched n).2 (hs n)

/-- **The embeddings along the tower.** -/
noncomputable def deningerCCEmbed (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) (n : ℕ) :
    (deningerCCTower S₀ sched n).carrier →* (deningerCCTower S₀ sched (n + 1)).carrier :=
  PushoutI.of (φ := deningerRootMap (deningerCCTower S₀ sched n).carrier
    (deningerCCRoot (deningerCCTower S₀ sched n) (sched n).1) (sched n).2) (ULift.up true)

/-- **The embeddings along the tower are injective.** -/
theorem deningerCCEmbed_injective (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerCCGood S₀) (n : ℕ) :
    Function.Injective (deningerCCEmbed S₀ sched n) :=
  PushoutI.of_injective
    (deningerRootMap_injective (deningerCCTower S₀ sched n).carrier
      (deningerCCRoot (deningerCCTower S₀ sched n) (sched n).1) (sched n).2
      (by have := hs n; omega)
      (deningerCCRoot_order (deningerCCTower S₀ sched n)
        (deningerCCTower_good S₀ sched hs h₀ n) (sched n).1))
    (ULift.up true)

/-- **The enumerated element of a stage acquires the scheduled root at the next stage.** -/
theorem deningerCCEmbed_root (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (h₀ : DeningerCCGood S₀) (n : ℕ) :
    ∃ y : (deningerCCTower S₀ sched (n + 1)).carrier,
      y ^ (sched n).2 =
        deningerCCEmbed S₀ sched n ((deningerCCTower S₀ sched n).hist (sched n).1) :=
  deningerCCStep_root (deningerCCTower S₀ sched n) (deningerCCTower_good S₀ sched hs h₀ n) n
    (sched n).1 (sched n).2

end RootAdjunction

end RHTower

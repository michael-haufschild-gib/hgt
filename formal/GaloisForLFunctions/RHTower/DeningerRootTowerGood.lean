import GaloisForLFunctions.RHTower.DeningerRootStageTower

/-!
# The tower of root adjunctions runs

Iterating the step of the tower preserves the invariant, so every stage of a tower which repeatedly
adjoins a root to the root last adjoined is a group with unique roots.  The invariant is not vacuous:
an infinite cyclic group with a generator satisfies it.

* `deningerRootTower` : the tower.
* `deningerRootTower_good` : every stage satisfies the invariant.
* `deningerGoodStage_int` : the infinite cyclic starting stage.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- **The tower of root adjunctions** attached to a choice of exponent at each stage. -/
noncomputable def deningerRootTower (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) :
    ℕ → DeningerRootStage.{u}
  | 0 => S₀
  | n + 1 => deningerRootStep (deningerRootTower S₀ ms n) (ms n)

/-- **Every stage of the tower satisfies the invariant.** -/
theorem deningerRootTower_good (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ)
    (hms : ∀ n, 2 ≤ (ms n).natAbs) (h₀ : DeningerGoodStage S₀) (n : ℕ) :
    DeningerGoodStage (deningerRootTower S₀ ms n) := by
  induction n with
  | zero => exact h₀
  | succ n ih => exact deningerRootStep_good _ (ms n) (hms n) ih

/-- **Every stage of the tower has unique roots.** -/
theorem deningerRootTower_uniqueRoots (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ)
    (hms : ∀ n, 2 ≤ (ms n).natAbs) (h₀ : DeningerGoodStage S₀) (n : ℕ)
    (x y : (deningerRootTower S₀ ms n).carrier) (k : ℕ) (hk : 0 < k) (h : x ^ k = y ^ k) :
    x = y :=
  (deningerRootTower_good S₀ ms hms h₀ n).uniqueRoots x y k hk h

/-- The infinite cyclic stage. -/
noncomputable def deningerIntStage : DeningerRootStage.{u} :=
  ⟨ULift.{u} (Multiplicative ℤ), deningerRootGen.{u}⟩

/-- **The infinite cyclic stage satisfies the invariant**, so the tower is not vacuous. -/
theorem deningerGoodStage_int : DeningerGoodStage deningerIntStage.{u} := by
  have hzp : ∀ x : ULift.{u} (Multiplicative ℤ), x ∈ Subgroup.zpowers deningerRootGen.{u} := by
    intro x
    refine ⟨Multiplicative.toAdd (MulEquiv.ulift x), ?_⟩
    show deningerRootGen.{u} ^ (Multiplicative.toAdd (MulEquiv.ulift x)) = x
    apply MulEquiv.ulift.injective
    apply Multiplicative.toAdd.injective
    simp [deningerRootGen]
  refine ⟨fun x y n hn h => deningerUliftInt_pow_inj x y n hn h,
    fun x n hn h => deningerUliftInt_torsionFree x n hn h, ?_,
    fun y n _ _ => hzp y, fun x _ => hzp x⟩
  intro n hn
  have h1 : Multiplicative.toAdd (MulEquiv.ulift (deningerRootGen.{u} ^ n)) = n := by
    simp [deningerRootGen]
  rw [show deningerRootGen.{u} ^ n = 1 from hn] at h1
  simpa using h1.symm

end RootAdjunction

end RHTower

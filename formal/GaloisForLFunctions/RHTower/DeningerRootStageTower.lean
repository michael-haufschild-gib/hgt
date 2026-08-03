import GaloisForLFunctions.RHTower.DeningerRootEltIsolated
import GaloisForLFunctions.RHTower.DeningerCentralizerZpow
import GaloisForLFunctions.RHTower.DeningerTower

/-!
# A tower of root adjunctions at the adjoined root

A stage of the tower is a group with a distinguished element; the step adjoins an `m`-th root to
that element and takes the root as the new distinguished element.  The five properties the step
needs — unique roots, torsion freeness, infinite order, isolation and self-centralization of the
distinguished element — are all inherited, so the tower runs.

* `DeningerRootStage`, `DeningerGoodStage`, `deningerRootStep` : the tower and its invariant.
* `deningerRootStep_good` : the inductive step.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- A stage of a tower of root adjunctions, with the element whose root is adjoined next. -/
structure DeningerRootStage : Type (u + 1) where
  /-- The underlying group of the stage. -/
  carrier : Type u
  /-- Its group structure. -/
  [group : Group carrier]
  /-- The distinguished element. -/
  elt : carrier

attribute [instance] DeningerRootStage.group

/-- The invariant carried along the tower. -/
structure DeningerGoodStage (S : DeningerRootStage.{u}) : Prop where
  /-- The stage has unique roots. -/
  uniqueRoots : ∀ (x y : S.carrier) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y
  /-- The stage is torsion free. -/
  torsionFree : ∀ (x : S.carrier) (n : ℕ), 0 < n → x ^ n = 1 → x = 1
  /-- The distinguished element has infinite order. -/
  order : ∀ n : ℤ, S.elt ^ n = 1 → n = 0
  /-- Its cyclic subgroup is isolated. -/
  isolated : ∀ (y : S.carrier) (n : ℕ), 0 < n → y ^ n ∈ Subgroup.zpowers S.elt →
    y ∈ Subgroup.zpowers S.elt
  /-- Its centralizer is that cyclic subgroup. -/
  central : ∀ x : S.carrier, x * S.elt * x⁻¹ = S.elt → x ∈ Subgroup.zpowers S.elt

/-- **The step of the tower**: adjoin an `m`-th root to the distinguished element and take it as the
new distinguished element. -/
noncomputable def deningerRootStep (S : DeningerRootStage.{u}) (m : ℤ) : DeningerRootStage.{u} :=
  ⟨PushoutI (deningerRootMap S.carrier S.elt m), deningerRootElt S.carrier S.elt m⟩

/-- **The inductive step of the tower.** -/
theorem deningerRootStep_good (S : DeningerRootStage.{u}) (m : ℤ) (hm2 : 2 ≤ m.natAbs)
    (hS : DeningerGoodStage S) : DeningerGoodStage (deningerRootStep S m) := by
  have hm : m ≠ 0 := by omega
  have hφ := deningerRootMap_injective S.carrier S.elt m hm hS.order
  have hcentA := deningerCentralizer_zpow_subset hS.uniqueRoots S.elt hS.central
  have htor : ∀ (g : PushoutI (deningerRootMap S.carrier S.elt m)) (n : ℕ), 0 < n → g ^ n = 1 →
      g = 1 := fun g n hn hg =>
    deningerRootAdjunction_torsionFree S.carrier S.elt m hm hS.order hS.torsionFree g n hn hg
  have hne : deningerRootElt S.carrier S.elt m ≠ 1 := by
    intro hc
    have h1 : PushoutI.of (φ := deningerRootMap S.carrier S.elt m) (ULift.up false)
        deningerRootGen.{u} =
        PushoutI.of (φ := deningerRootMap S.carrier S.elt m) (ULift.up false) 1 := by
      rw [map_one]
      exact hc
    have h2 : deningerRootGen.{u} = 1 := PushoutI.of_injective hφ _ h1
    have h3 : Multiplicative.ofAdd (1 : ℤ) = 1 := by
      have h4 := congrArg (MulEquiv.ulift (α := Multiplicative ℤ)) h2
      simp [deningerRootGen] at h4
    have := congrArg Multiplicative.toAdd h3
    simp at this
  refine ⟨?_, htor, ?_, ?_, ?_⟩
  · intro x y n hn hxy
    exact deningerRootAdjunction_uniqueRoots S.carrier S.elt m hm hS.order hS.uniqueRoots
      hS.isolated hcentA hS.torsionFree x y (n - 1) (by
        rw [show n - 1 + 1 = n by omega]; exact hxy)
  · intro n hn
    exact deningerInfiniteOrder (deningerRootElt S.carrier S.elt m) hne htor n hn
  · intro y n hn hy
    exact deningerRootElt_isolated S.carrier S.elt m hm hS.order hcentA hS.uniqueRoots
      hS.isolated hS.torsionFree y n hn hy
  · intro x hx
    refine deningerRootElt_centralizer S.carrier S.elt m hm hm2 hS.order x ?_
    exact mul_inv_eq_iff_eq_mul.mp hx

end RootAdjunction

end RHTower

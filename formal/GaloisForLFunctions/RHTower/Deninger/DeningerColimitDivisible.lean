import GaloisForLFunctions.RHTower.Deninger.DeningerRootStepCyclic

/-!
# Divisibility in the colimit of the tower

Every stage of a tower started at a cyclic stage is cyclic, and the image of the distinguished
element of a later stage is a prefix product power of the image of an earlier one.  So if every
exponent divides some prefix product, every element of the colimit has a root of that exponent.

* `deningerRootTower_cyclic` : every stage is cyclic.
* `deningerTowerColimit_elt_pow` : the prefix product relation.
* `deningerTowerColimit_divisible` : divisibility of the colimit.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- **Every stage of the tower is cyclic**, if the starting stage is. -/
theorem deningerRootTower_cyclic (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ)
    (hms : ∀ n, 2 ≤ (ms n).natAbs) (h₀ : DeningerGoodStage S₀)
    (hgen₀ : ∀ x : S₀.carrier, x ∈ Subgroup.zpowers S₀.elt) (n : ℕ) :
    ∀ x : (deningerRootTower S₀ ms n).carrier,
      x ∈ Subgroup.zpowers (deningerRootTower S₀ ms n).elt := by
  induction n with
  | zero => exact hgen₀
  | succ n ih =>
    have hgood := deningerRootTower_good S₀ ms hms h₀ n
    exact fun x => deningerRootStep_cyclic (deningerRootTower S₀ ms n).carrier
      (deningerRootTower S₀ ms n).elt (ms n) (by have := hms n; omega) hgood.order ih x

/-- **The prefix product relation between the images of the distinguished elements.** -/
theorem deningerTowerColimit_elt_pow (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ) (n k : ℕ)
    (h : n ≤ k) :
    (deningerTowerIota S₀ ms k (deningerRootTower S₀ ms k).elt) ^
        (∏ i ∈ Finset.Ico n k, ms i) =
      deningerTowerIota S₀ ms n (deningerRootTower S₀ ms n).elt := by
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.prod_Ico_succ_top hk, mul_comm, zpow_mul, deningerTowerColimit_root]
    exact ih

/-- **Divisibility of the colimit**, when every exponent divides some prefix product. -/
theorem deningerTowerColimit_divisible (S₀ : DeningerRootStage.{u}) (ms : ℕ → ℤ)
    (hms : ∀ n, 2 ≤ (ms n).natAbs) (h₀ : DeningerGoodStage S₀)
    (hgen₀ : ∀ x : S₀.carrier, x ∈ Subgroup.zpowers S₀.elt)
    (hfair : ∀ (n : ℕ) (N : ℤ), N ≠ 0 → ∃ k, n ≤ k ∧ N ∣ ∏ i ∈ Finset.Ico n k, ms i)
    (x : deningerTowerColimit S₀ ms) (N : ℤ) (hN : N ≠ 0) :
    ∃ y : deningerTowerColimit S₀ ms, y ^ N = x := by
  obtain ⟨n, a, ha⟩ := deningerTowerColimit_surjective S₀ ms x
  obtain ⟨c, hc'⟩ := deningerRootTower_cyclic S₀ ms hms h₀ hgen₀ n a
  have hc : (deningerRootTower S₀ ms n).elt ^ c = a := hc'
  obtain ⟨k, hk, Q, hQ⟩ := hfair n N hN
  refine ⟨(deningerTowerIota S₀ ms k (deningerRootTower S₀ ms k).elt) ^ (Q * c), ?_⟩
  have hstep : (deningerTowerIota S₀ ms k (deningerRootTower S₀ ms k).elt) ^ (N * Q) =
      deningerTowerIota S₀ ms n (deningerRootTower S₀ ms n).elt := by
    rw [← hQ]
    exact deningerTowerColimit_elt_pow S₀ ms n k hk
  calc ((deningerTowerIota S₀ ms k (deningerRootTower S₀ ms k).elt) ^ (Q * c)) ^ N
      = ((deningerTowerIota S₀ ms k (deningerRootTower S₀ ms k).elt) ^ (N * Q)) ^ c := by
        rw [← zpow_mul, ← zpow_mul]
        ring_nf
    _ = (deningerTowerIota S₀ ms n (deningerRootTower S₀ ms n).elt) ^ c := by rw [hstep]
    _ = x := by
        rw [← map_zpow]
        show deningerTowerIota S₀ ms n ((deningerRootTower S₀ ms n).elt ^ c) = x
        rw [hc]
        exact ha

end RootAdjunction

end RHTower

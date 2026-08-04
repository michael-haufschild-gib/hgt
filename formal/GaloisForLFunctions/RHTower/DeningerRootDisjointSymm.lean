import GaloisForLFunctions.RHTower.DeningerRootInherit

/-!
# Disjointness of the adjoined root from the waiting elements

The disjointness of a waiting element from the cyclic factor is symmetric: no conjugate of a nonzero
power of the adjoined root is a power of a waiting element either.  Conjugating the relation the
other way exchanges the two sides, and the case of a trivial exponent is the infinite order of the
adjoined root.

* `deningerRootAdjunction_disjoint_symm` : the symmetric disjointness.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- **The symmetric disjointness.** -/
theorem deningerRootAdjunction_disjoint_symm (hm : m ≠ 0)
    (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (htorA : ∀ (x : A) (n : ℕ), 0 < n → x ^ n = 1 → x = 1) (u : A)
    (hdisj : ∀ (x : A) (c : ℤ), c ≠ 0 → ∀ k : ULift.{u} (Multiplicative ℤ),
      x⁻¹ * u ^ c * x ≠ deningerRootMap A a m (ULift.up true) k)
    (w : PushoutI (deningerRootMap A a m)) (c : ℤ) (hc : c ≠ 0) (k : ℤ) :
    w⁻¹ * (deningerRootElt A a m) ^ c * w ≠
      (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) ^ k := by
  intro hcon
  have hne : deningerRootElt A a m ≠ 1 := by
    intro hc1
    have h1 : PushoutI.of (φ := deningerRootMap A a m) (ULift.up false) deningerRootGen.{u} =
        PushoutI.of (φ := deningerRootMap A a m) (ULift.up false) 1 := by
      rw [map_one]
      exact hc1
    exact deningerRootGen_ne_one
      (PushoutI.of_injective (deningerRootMap_injective A a m hm ha) _ h1)
  have hord : ∀ n : ℤ, (deningerRootElt A a m) ^ n = 1 → n = 0 :=
    deningerInfiniteOrder (deningerRootElt A a m) hne
      (fun g n hn hg => deningerRootAdjunction_torsionFree A a m hm ha htorA g n hn hg)
  by_cases hk : k = 0
  · subst hk
    refine hc (hord c ?_)
    rw [zpow_zero] at hcon
    have h2 : (deningerRootElt A a m) ^ c = w * 1 * w⁻¹ := by
      rw [← hcon]
      group
    rw [h2]
    group
  · refine deningerRootAdjunction_disjoint A a m hm ha u hdisj w⁻¹ k hk
      (deningerRootGen.{u} ^ c) ?_
    rw [inv_inv]
    have h3 : PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)
        (deningerRootGen.{u} ^ c) = (deningerRootElt A a m) ^ c :=
      map_zpow (PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)) deningerRootGen.{u} c
    rw [h3, ← hcon]
    group

end RootAdjunction

end RHTower

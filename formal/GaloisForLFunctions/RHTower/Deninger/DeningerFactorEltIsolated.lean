import GaloisForLFunctions.RHTower.Deninger.DeningerFactorEltCentral

/-!
# Isolation is inherited by elements of the factor

If no conjugate of a nonzero power of an element of the group factor lies in the base group, then
anything whose positive power is a power of it commutes with that power, hence lies in the factor by
the centralizer criterion, and isolation inside the factor finishes.  The hypothesis cannot be
dropped: the element whose root is adjoined acquires one, so its cyclic subgroup stops being
isolated.

* `deningerRootAdjunction_isolated` : the inheritance.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- The power computation, inside the group factor. -/
theorem deningerRootFactorTrue_isolated (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (u x : deningerRootFactor A (ULift.up true)) (c : ℤ) (n : ℕ)
    (hiso : ∀ y : deningerRootFactor A (ULift.up true), ∀ j : ℕ, 0 < j →
      y ^ j ∈ Subgroup.zpowers u → y ∈ Subgroup.zpowers u)
    (hn : 0 < n)
    (h : PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) (x ^ n) =
      PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) (u ^ c)) :
    x ∈ Subgroup.zpowers u := by
  have hxn : x ^ n = u ^ c :=
    PushoutI.of_injective (deningerRootMap_injective A a m hm ha) (ULift.up true) h
  exact hiso x n hn ⟨c, hxn.symm⟩

/-- **Isolation is inherited by elements of the group factor** whose nonzero powers never conjugate
into the base group. -/
theorem deningerRootAdjunction_isolated (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (htorA : ∀ (x : A) (n : ℕ), 0 < n → x ^ n = 1 → x = 1)
    (u : A)
    (hdisj : ∀ (x : A) (c : ℤ), c ≠ 0 → ∀ k : ULift.{u} (Multiplicative ℤ),
      x⁻¹ * u ^ c * x ≠ deningerRootMap A a m (ULift.up true) k)
    (hiso : ∀ (y : A) (j : ℕ), 0 < j → y ^ j ∈ Subgroup.zpowers u → y ∈ Subgroup.zpowers u)
    (y : PushoutI (deningerRootMap A a m)) (n : ℕ) (hn : 0 < n)
    (hy : y ^ n ∈ Subgroup.zpowers
      (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u)) :
    y ∈ Subgroup.zpowers (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerRootMap A a m)
    (deningerRootMap_injective A a m hm ha)
  obtain ⟨c, hc'⟩ := hy
  have hc : (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) ^ c = y ^ n := hc'
  have hcof : PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) (u ^ c) = y ^ n := by
    rw [← hc]
    exact map_zpow (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true)) u c
  by_cases hc0 : c = 0
  · subst hc0
    rw [zpow_zero] at hcof
    have hy1 : y ^ n = 1 := by
      refine hcof.symm.trans ?_
      exact map_one (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true))
    have hy0 : y = 1 :=
      deningerRootAdjunction_torsionFree A a m hm ha htorA y n hn hy1
    exact ⟨0, by simp [hy0]⟩
  · have hune : (u ^ c : deningerRootFactor A (ULift.up true)) ∉
        (deningerRootMap A a m (ULift.up true)).range := by
      rintro ⟨k, hk⟩
      refine hdisj 1 c hc0 k ?_
      rw [inv_one, one_mul, mul_one]
      exact hk.symm
    obtain ⟨x, hx⟩ | ⟨x', k, hk⟩ :=
      deningerCentralizer_factor (d := d) (ULift.up true) (u ^ c) hune y (by
        rw [hcof]
        exact (Commute.refl y).pow_right n)
    · have hxn : PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) (x ^ n) =
          PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) (u ^ c) := by
        rw [map_pow, ← hx]
        exact hcof.symm
      obtain ⟨e, he⟩ := deningerRootFactorTrue_isolated A a m hm ha u x c n hiso hn hxn
      refine ⟨e, ?_⟩
      show (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) ^ e = y
      rw [← map_zpow, hx]
      exact congrArg (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true)) he
    · exact absurd hk (hdisj x' c hc0 k)

end RootAdjunction

end RHTower

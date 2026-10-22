import GaloisForLFunctions.RHTower.Deninger.DeningerFreeGroupDisjoint

/-!
# The three properties of a waiting element are inherited together

An element of the group factor which is disjoint from the subgroup whose root is adjoined keeps all
three properties a tower needs of it: its centralizer, the isolation of its cyclic subgroup, and its
disjointness from the new cyclic factor.  Packaging them together is what a stage carrying a family
of elements has to apply at each of them.

* `deningerRootAdjunction_inherit` : the three properties, together.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- **The three properties of a waiting element are inherited together.** -/
theorem deningerRootAdjunction_inherit (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (htorA : ∀ (x : A) (n : ℕ), 0 < n → x ^ n = 1 → x = 1) (u : A)
    (hdisj : ∀ (x : A) (c : ℤ), c ≠ 0 → ∀ k : ULift.{u} (Multiplicative ℤ),
      x⁻¹ * u ^ c * x ≠ deningerRootMap A a m (ULift.up true) k)
    (hC : ∀ x : A, x * u * x⁻¹ = u → x ∈ Subgroup.zpowers u)
    (hiso : ∀ (y : A) (n : ℕ), 0 < n → y ^ n ∈ Subgroup.zpowers u → y ∈ Subgroup.zpowers u) :
    (∀ w : PushoutI (deningerRootMap A a m),
        w * PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u =
          PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u * w →
        w ∈ Subgroup.zpowers
          (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u)) ∧
      (∀ (y : PushoutI (deningerRootMap A a m)) (n : ℕ), 0 < n →
        y ^ n ∈ Subgroup.zpowers
            (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) →
        y ∈ Subgroup.zpowers
          (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u)) ∧
      (∀ (w : PushoutI (deningerRootMap A a m)) (c : ℤ), c ≠ 0 →
        ∀ e : deningerRootFactor A (ULift.up false),
        w⁻¹ * (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) ^ c * w ≠
          PushoutI.of (φ := deningerRootMap A a m) (ULift.up false) e) := by
  have hu : u ∉ (deningerRootMap A a m (ULift.up true)).range := by
    rintro ⟨k, hk⟩
    refine hdisj 1 1 one_ne_zero k ?_
    rw [inv_one, one_mul, mul_one, zpow_one]
    exact hk.symm
  have hesc : ¬ ∃ (x : A) (k : ULift.{u} (Multiplicative ℤ)),
      x⁻¹ * u * x = deningerRootMap A a m (ULift.up true) k := by
    rintro ⟨x, k, hk⟩
    refine hdisj x 1 one_ne_zero k ?_
    rw [zpow_one]
    exact hk
  refine ⟨fun w hw => deningerRootAdjunction_selfCentralizing A a m hm ha u hu hesc hC w hw,
    fun y n hn hy => deningerRootAdjunction_isolated A a m hm ha htorA u hdisj hiso y n hn hy,
    fun w c hc e => deningerRootAdjunction_disjoint A a m hm ha u hdisj w c hc e⟩

end RootAdjunction

end RHTower

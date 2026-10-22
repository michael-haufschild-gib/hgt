import GaloisForLFunctions.RHTower.Deninger.DeningerFairExponents

/-!
# Self-centralization is inherited by elements of the factor

An element of the group factor which does not conjugate into the base group inside that factor keeps
its centralizer: anything commuting with it in the amalgam lies in the factor, by the centralizer
criterion for factor elements, and there it centralizes the element.  So an element whose
centralizer in the factor is the cyclic subgroup it generates has the same property in the amalgam.

* `deningerRootAdjunction_selfCentralizing` : the inheritance.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- The commuting computation, inside the group factor. -/
theorem deningerRootFactorTrue_mem (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (u x : deningerRootFactor A (ULift.up true))
    (hC : ∀ y : deningerRootFactor A (ULift.up true), y * u * y⁻¹ = u →
      y ∈ Subgroup.zpowers u)
    (h : PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) x *
        PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u =
      PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u *
        PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) x) :
    x ∈ Subgroup.zpowers u := by
  have hxu : x * u = u * x := by
    refine PushoutI.of_injective (deningerRootMap_injective A a m hm ha) (ULift.up true) ?_
    rw [map_mul, map_mul]
    exact h
  refine hC x ?_
  rw [hxu]
  group

/-- **Self-centralization is inherited by elements of the group factor.** -/
theorem deningerRootAdjunction_selfCentralizing (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (u : A) (hu : u ∉ (deningerRootMap A a m (ULift.up true)).range)
    (hesc : ¬ ∃ (x : A) (k : ULift.{u} (Multiplicative ℤ)),
      x⁻¹ * u * x = deningerRootMap A a m (ULift.up true) k)
    (hC : ∀ x : A, x * u * x⁻¹ = u → x ∈ Subgroup.zpowers u)
    (w : PushoutI (deningerRootMap A a m))
    (hcomm : w * PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u =
      PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u * w) :
    w ∈ Subgroup.zpowers
      (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerRootMap A a m)
    (deningerRootMap_injective A a m hm ha)
  obtain ⟨x, hx⟩ | hesc' :=
    deningerCentralizer_factor (d := d) (ULift.up true) u hu w hcomm
  · have hcomm' : PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) x *
        PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u =
        PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u *
        PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) x := by
      rw [← hx]
      exact hcomm
    obtain ⟨c, hc⟩ := deningerRootFactorTrue_mem A a m hm ha u x hC hcomm'
    refine ⟨c, ?_⟩
    show (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) ^ c = w
    rw [← map_zpow, hx]
    exact congrArg (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true)) hc
  · exact absurd hesc' hesc

end RootAdjunction

end RHTower

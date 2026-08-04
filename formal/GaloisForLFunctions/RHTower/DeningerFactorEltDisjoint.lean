import GaloisForLFunctions.RHTower.DeningerFactorImages

/-!
# Disjointness from the cyclic factor is inherited

If no conjugate of a nonzero power of an element of the group factor lies in the base group, then no
conjugate of a nonzero power of its image lies in the cyclic factor: the conjugacy criterion for
short elements puts the conjugator inside the group factor, and then the conjugate lies in both
factor images, hence in the base group, which the hypothesis forbids.

* `deningerRootAdjunction_disjoint` : the inheritance.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- **Disjointness from the cyclic factor is inherited.** -/
theorem deningerRootAdjunction_disjoint (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0) (u : A)
    (hdisj : ∀ (x : A) (c : ℤ), c ≠ 0 → ∀ k : ULift.{u} (Multiplicative ℤ),
      x⁻¹ * u ^ c * x ≠ deningerRootMap A a m (ULift.up true) k)
    (w : PushoutI (deningerRootMap A a m)) (c : ℤ) (hc : c ≠ 0)
    (e : deningerRootFactor A (ULift.up false)) :
    w⁻¹ * (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) ^ c * w ≠
      PushoutI.of (φ := deningerRootMap A a m) (ULift.up false) e := by
  classical
  intro hcon
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerRootMap A a m)
    (deningerRootMap_injective A a m hm ha)
  set v : deningerRootFactor A (ULift.up true) := u ^ c with hv
  have hune : v ∉ (deningerRootMap A a m (ULift.up true)).range := by
    rintro ⟨k, hk⟩
    refine hdisj 1 c hc k ?_
    rw [inv_one, one_mul, mul_one]
    exact hk.symm
  have hpow : (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) ^ c =
      PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) v :=
    (map_zpow (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true)) u c).symm
  rw [hpow] at hcon
  have hshort : deningerLen d (w⁻¹ *
      PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) v * w) ≤ 1 := by
    rw [hcon]
    exact deningerLen_of_le_one (d := d) (ULift.up false) e
  obtain ⟨x, hx⟩ | ⟨x', k, hk⟩ :=
    deningerShortConj_cases (d := d) (ULift.up true) v hune w hshort
  · have hcross : PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) (x⁻¹ * v * x) =
        PushoutI.of (φ := deningerRootMap A a m) (ULift.up false) e := by
      rw [← hcon, hx, map_mul, map_mul, map_inv]
    obtain ⟨k, hk⟩ := deningerOf_eq_cross (d := d)
      (deningerRootMap_injective A a m hm ha) (ULift.up true) (ULift.up false)
      (by simp) _ e hcross
    exact hdisj x c hc k hk.symm
  · exact hdisj x' c hc k hk

end RootAdjunction

end RHTower

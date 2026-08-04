import GaloisForLFunctions.RHTower.DeningerRootDisjointSymm

/-!
# Disjointness between two waiting elements survives an adjunction

Two elements of the group factor which are disjoint there, and each disjoint from the subgroup being
rooted, stay disjoint in the amalgam: a conjugate of a power of the first which is a power of the
second is short, so the conjugator lies in the group factor and the relation descends to it.

* `deningerRootAdjunction_disjoint_factors` : the disjointness.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- **Disjointness between two waiting elements survives an adjunction.** -/
theorem deningerRootAdjunction_disjoint_factors (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (u v : A)
    (hdisjU : ∀ (x : A) (c : ℤ), c ≠ 0 → ∀ k : ULift.{u} (Multiplicative ℤ),
      x⁻¹ * u ^ c * x ≠ deningerRootMap A a m (ULift.up true) k)
    (hUV : ∀ (x : A) (c : ℤ), c ≠ 0 → ∀ k : ℤ, x⁻¹ * u ^ c * x ≠ v ^ k)
    (w : PushoutI (deningerRootMap A a m)) (c : ℤ) (hc : c ≠ 0) (k : ℤ) :
    w⁻¹ * (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) ^ c * w ≠
      (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) v) ^ k := by
  classical
  intro hcon
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerRootMap A a m)
    (deningerRootMap_injective A a m hm ha)
  set y : deningerRootFactor A (ULift.up true) := u ^ c with hy
  set z : deningerRootFactor A (ULift.up true) := v ^ k with hz
  have hyr : y ∉ (deningerRootMap A a m (ULift.up true)).range := by
    rintro ⟨p, hp⟩
    refine hdisjU 1 c hc p ?_
    rw [inv_one, one_mul, mul_one]
    exact hp.symm
  have hpowy : (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) u) ^ c =
      PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) y :=
    (map_zpow (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true)) u c).symm
  have hpowz : (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) v) ^ k =
      PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) z :=
    (map_zpow (PushoutI.of (φ := deningerRootMap A a m) (ULift.up true)) v k).symm
  rw [hpowy, hpowz] at hcon
  have hshort : deningerLen d (w⁻¹ *
      PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) y * w) ≤ 1 := by
    rw [hcon]
    exact deningerLen_of_le_one (d := d) (ULift.up true) z
  obtain ⟨x, hx⟩ | ⟨x', p, hp⟩ :=
    deningerShortConj_cases (d := d) (ULift.up true) y hyr w hshort
  · have hfac : PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) (x⁻¹ * y * x) =
        PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) z := by
      rw [← hcon, hx, map_mul, map_mul, map_inv]
    exact hUV x c hc k
      (PushoutI.of_injective (deningerRootMap_injective A a m hm ha) (ULift.up true) hfac)
  · exact hdisjU x' c hc p hp

end RootAdjunction

end RHTower

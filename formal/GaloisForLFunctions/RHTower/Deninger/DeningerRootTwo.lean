import GaloisForLFunctions.RHTower.Deninger.DeningerRootIndex

/-!
# Degree two across a root adjunction

Adjoining a root to a group leaves the second homology zero, over a field of characteristic zero.
The base group has finite index in the infinite cyclic factor, so the index is invertible and the
comparison map of the tree sequence is injective.

* `deningerRootAdjunction_isZero_two` : the root adjunction step in degree two.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory CategoryTheory.Limits

universe u

namespace RootAdjunction

/-- **Adjoining a root preserves the vanishing of the second homology.** -/
theorem deningerRootAdjunction_isZero_two (A : Type u) [Group A] (a : A) (m : ℤ) (hm : m ≠ 0)
    (ha : ∀ n : ℤ, a ^ n = 1 → n = 0) (k : Type u) [Field k] [CharZero k]
    (hA : IsZero (groupHomology (Rep.trivial k A k) 2)) :
    IsZero (groupHomology
      (Rep.trivial k (PushoutI (deningerRootMap A a m)) k) 2) := by
  classical
  have hφ := deningerRootMap_injective A a m hm ha
  have hindex : ((((PushoutI.base (deningerRootMap A a m)).range).subgroupOf
      ((PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)).range))).index = m.natAbs := by
    rw [deningerIndex_subgroupOf hφ, deningerRootMap_range_index]
  have hne : m.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hm
  haveI : Finite (↥(PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)).range ⧸
      (((PushoutI.base (deningerRootMap A a m)).range).subgroupOf
        ((PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)).range))) :=
    Nat.finite_of_card_ne_zero (by rw [show Nat.card _ = _ from hindex]; exact hne)
  haveI : Fintype (↥(PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)).range ⧸
      (((PushoutI.base (deningerRootMap A a m)).range).subgroupOf
        ((PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)).range))) :=
    Fintype.ofFinite _
  have hcardeq : Fintype.card (↥(PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)).range ⧸
      (((PushoutI.base (deningerRootMap A a m)).range).subgroupOf
        ((PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)).range))) = m.natAbs := by
    rw [← Nat.card_eq_fintype_card]
    exact hindex
  exact deningerAmalgam_isZero_two k hφ MulEquiv.ulift MulEquiv.ulift
    (by rw [hcardeq]; exact_mod_cast hne) hA

end RootAdjunction

end RHTower

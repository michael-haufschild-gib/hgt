import GaloisForLFunctions.RHTower.DeningerConjBase
import GaloisForLFunctions.RHTower.DeningerRGroupConjugation

/-!
# A root adjunction does not move its base group

For a root adjunction at an isolated element of a group with unique roots, a factor element which
conjugates a base group element into the base group leaves it fixed.  On the infinite cyclic factor
this is commutativity; on the group itself it is the rigidity of conjugation of an isolated element.
Combined with the propagation from letters to words, conjugation by any word of the amalgam leaves
the base group pointwise fixed.

* `deningerUliftInt_conj` : the cyclic factor is commutative.
* `deningerRootTrue_conj` : the group factor does not move the powers of the adjoined element.
* `deningerRootHcent` : the hypothesis on the factors, for a root adjunction.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- **The cyclic factor is commutative**, so conjugation there is trivial. -/
theorem deningerUliftInt_conj (x y z : ULift.{u} (Multiplicative ℤ))
    (h : x * y * x⁻¹ = z) : y = z := by
  rw [← h]
  apply MulEquiv.ulift.injective
  apply Multiplicative.toAdd.injective
  simp

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- The cyclic factor of a root adjunction is commutative. -/
theorem deningerRootFactorFalse_conj (x y z : deningerRootFactor A (ULift.up false))
    (h : x * y * x⁻¹ = z) : y = z :=
  deningerUliftInt_conj x y z h

/-- The structure map into the group factor is the power map. -/
theorem deningerRootMap_true_apply (u : ULift.{u} (Multiplicative ℤ)) :
    deningerRootMap A a m (ULift.up true) u = a ^ (Multiplicative.toAdd (MulEquiv.ulift u)) :=
  rfl

/-- **The group factor does not move the powers of the adjoined element** when that element is
isolated and the group has unique roots. -/
theorem deningerRootTrue_conj
    (hA : ∀ (x y : A) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y)
    (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (hiso : ∀ (y : A) (n : ℕ), 0 < n → y ^ n ∈ Subgroup.zpowers a → y ∈ Subgroup.zpowers a)
    (x : A) (cu cv : ℤ) (h : x * a ^ cu * x⁻¹ = a ^ cv) : cv = cu := by
  by_cases hcu : cu = 0
  · subst hcu
    rw [zpow_zero, mul_one, mul_inv_cancel] at h
    exact ha cv h.symm
  · have hfix : x * a * x⁻¹ = a := deningerConj_zpow_fixes hA a ha hiso x cu cv hcu h
    have hpow : x * a ^ cu * x⁻¹ = a ^ cu := by
      rw [← deningerConj_zpow_eq, hfix]
    have : a ^ cv = a ^ cu := by rw [← h, hpow]
    have hone : a ^ (cv - cu) = 1 := by
      rw [sub_eq_add_neg, zpow_add, this, zpow_neg, mul_inv_cancel]
    have := ha _ hone
    omega

/-- **The hypothesis on the factors, for a root adjunction** at an isolated element of a group with
unique roots. -/
theorem deningerRootHcent (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (hA : ∀ (x y : A) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y)
    (hiso : ∀ (y : A) (n : ℕ), 0 < n → y ^ n ∈ Subgroup.zpowers a → y ∈ Subgroup.zpowers a)
    (i : ULift Bool) (x : deningerRootFactor A i) (u v : ULift.{u} (Multiplicative ℤ))
    (h : x * deningerRootMap A a m i u * x⁻¹ = deningerRootMap A a m i v) : v = u := by
  have hφ := deningerRootMap_injective A a m hm ha
  obtain ⟨b⟩ := i
  cases b
  · exact (hφ (ULift.up false) (deningerRootFactorFalse_conj A x _ _ h)).symm
  · refine hφ (ULift.up true) ?_
    have hcu : deningerRootMap A a m (ULift.up true) u =
        a ^ (Multiplicative.toAdd (MulEquiv.ulift u)) := deningerRootMap_true_apply A a m u
    have hcv : deningerRootMap A a m (ULift.up true) v =
        a ^ (Multiplicative.toAdd (MulEquiv.ulift v)) := deningerRootMap_true_apply A a m v
    have hzz : (Multiplicative.toAdd (MulEquiv.ulift v)) =
        (Multiplicative.toAdd (MulEquiv.ulift u)) := by
      refine deningerRootTrue_conj A a hA ha hiso x _ _ ?_
      rw [← hcu, ← hcv]
      exact h
    rw [hcu, hcv, hzz]

end RootAdjunction

end RHTower

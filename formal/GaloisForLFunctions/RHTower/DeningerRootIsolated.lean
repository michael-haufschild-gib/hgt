import GaloisForLFunctions.RHTower.DeningerFactorMix
import GaloisForLFunctions.RHTower.DeningerRootIndex

/-!
# Roots of elements of the factors of a root adjunction

The infinite cyclic factor of a root adjunction is never isolated over its base group, so the
criterion for uniqueness of roots over an isolated base does not apply to it.  It does not have to:
when an element of the group and an element of the cyclic factor have the same power in the base
group, isolation of the adjoined element inside the group alone forces both into the base group,
because the exponents then match on the nose.  So a root adjunction at an isolated element has
unique roots for the elements of its factors.

* `deningerUliftInt_pow_inj` : an infinite cyclic group has unique roots.
* `deningerRootMap_true_mem_iff` : the base group inside the group is the powers of the element.
* `deningerRootMix` : the mixing hypothesis for a root adjunction at an isolated element.
* `deningerRootAdjunction_pow_eq_of_factors` : uniqueness of roots for elements of the factors.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- **An infinite cyclic group has unique roots.** -/
theorem deningerUliftInt_pow_inj (y z : ULift.{u} (Multiplicative ℤ)) (n : ℕ) (hn : 0 < n)
    (h : y ^ n = z ^ n) : y = z := by
  apply MulEquiv.ulift.injective
  apply Multiplicative.toAdd.injective
  have h1 : Multiplicative.toAdd (MulEquiv.ulift (y ^ n)) =
      Multiplicative.toAdd (MulEquiv.ulift (z ^ n)) := by rw [h]
  simp only [map_pow, toAdd_pow, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (by omega)) h1

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- The cyclic factor of a root adjunction has unique roots. -/
theorem deningerRootFactorFalse_pow_inj (y z : deningerRootFactor A (ULift.up false)) (n : ℕ)
    (hn : 0 < n) (h : y ^ n = z ^ n) : y = z :=
  deningerUliftInt_pow_inj y z n hn h

/-- The base group of a root adjunction sits in the group as the powers of the element whose root
is adjoined. -/
theorem deningerRootMap_true_mem_iff (x : A) :
    x ∈ (deningerRootMap A a m (ULift.up true)).range ↔ ∃ k : ℤ, a ^ k = x := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨Multiplicative.toAdd (MulEquiv.ulift w), rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨MulEquiv.ulift.symm (Multiplicative.ofAdd k), rfl⟩

/-- The mixed case of the mixing hypothesis: an element of the group and an element of the cyclic
factor whose common power lies in the base group both lie in the base group. -/
theorem deningerRootMix_true_false (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (hiso : ∀ (x : A) (n : ℕ), 0 < n →
      x ^ n ∈ (deningerRootMap A a m (ULift.up true)).range →
      x ∈ (deningerRootMap A a m (ULift.up true)).range)
    (x : deningerRootFactor A (ULift.up true)) (y : deningerRootFactor A (ULift.up false))
    (n : ℕ) (hn : 0 < n)
    (hx : x ^ n ∈ (deningerRootMap A a m (ULift.up true)).range)
    (hy : y ^ n ∈ (deningerRootMap A a m (ULift.up false)).range)
    (h : PushoutI.of (φ := deningerRootMap A a m) (ULift.up true) (x ^ n) =
      PushoutI.of (φ := deningerRootMap A a m) (ULift.up false) (y ^ n)) :
    x ∈ (deningerRootMap A a m (ULift.up true)).range ∧
      y ∈ (deningerRootMap A a m (ULift.up false)).range := by
  have hφ := deningerRootMap_injective A a m hm ha
  obtain ⟨w, hw⟩ := hiso x n hn hx
  obtain ⟨v, hv⟩ := hy
  refine ⟨⟨w, hw⟩, ?_⟩
  have hxn : x ^ n = deningerRootMap A a m (ULift.up true) (w ^ n) := by
    rw [map_pow, hw]
  have hbase : PushoutI.base (deningerRootMap A a m) (w ^ n) =
      PushoutI.base (deningerRootMap A a m) v := by
    rw [← PushoutI.of_apply_eq_base (deningerRootMap A a m) (ULift.up true) (w ^ n),
      ← PushoutI.of_apply_eq_base (deningerRootMap A a m) (ULift.up false) v, ← hxn, hv]
    exact h
  have hwv : w ^ n = v := PushoutI.base_injective hφ hbase
  refine ⟨w, ?_⟩
  have hpow : (deningerRootMap A a m (ULift.up false) w) ^ n = y ^ n := by
    rw [← map_pow, hwv, hv]
  exact deningerRootFactorFalse_pow_inj A _ y n hn hpow

/-- **The mixing hypothesis for a root adjunction at an isolated element.** -/
theorem deningerRootMix (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (hiso : ∀ (x : A) (n : ℕ), 0 < n →
      x ^ n ∈ (deningerRootMap A a m (ULift.up true)).range →
      x ∈ (deningerRootMap A a m (ULift.up true)).range)
    (i j : ULift Bool) (hij : i ≠ j) (x : deningerRootFactor A i) (y : deningerRootFactor A j)
    (n : ℕ) (hn : 0 < n)
    (hx : x ^ n ∈ (deningerRootMap A a m i).range)
    (hy : y ^ n ∈ (deningerRootMap A a m j).range)
    (h : PushoutI.of (φ := deningerRootMap A a m) i (x ^ n) =
      PushoutI.of (φ := deningerRootMap A a m) j (y ^ n)) :
    x ∈ (deningerRootMap A a m i).range ∧ y ∈ (deningerRootMap A a m j).range := by
  obtain ⟨bi⟩ := i
  obtain ⟨bj⟩ := j
  cases bi <;> cases bj
  · exact absurd rfl hij
  · exact (deningerRootMix_true_false A a m hm ha hiso y x n hn hy hx h.symm).symm
  · exact deningerRootMix_true_false A a m hm ha hiso x y n hn hx hy h
  · exact absurd rfl hij

/-- **Uniqueness of roots for elements of the factors of a root adjunction** at an isolated
element. -/
theorem deningerRootAdjunction_pow_eq_of_factors (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (hA : ∀ (x y : A) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y)
    (hiso : ∀ (x : A) (n : ℕ), 0 < n →
      x ^ n ∈ (deningerRootMap A a m (ULift.up true)).range →
      x ∈ (deningerRootMap A a m (ULift.up true)).range)
    (i j : ULift Bool) (x : deningerRootFactor A i) (y : deningerRootFactor A j)
    (n : ℕ) (hn : 0 < n)
    (h : (PushoutI.of (φ := deningerRootMap A a m) i x) ^ n =
      (PushoutI.of (φ := deningerRootMap A a m) j y) ^ n) :
    PushoutI.of (φ := deningerRootMap A a m) i x =
      PushoutI.of (φ := deningerRootMap A a m) j y := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerRootMap A a m)
    (deningerRootMap_injective A a m hm ha)
  refine deningerPow_eq_of_factors_mix (d := d) (deningerRootMap_injective A a m hm ha)
    (fun p q r hr hpq => deningerUliftInt_pow_inj p q r hr hpq) ?_
    (deningerRootMix A a m hm ha hiso) i j x y n hn h
  rintro ⟨b⟩
  cases b
  · exact fun p q r hr hpq => deningerRootFactorFalse_pow_inj A p q r hr hpq
  · exact fun p q r hr hpq => hA p q r hr hpq

end RootAdjunction

end RHTower

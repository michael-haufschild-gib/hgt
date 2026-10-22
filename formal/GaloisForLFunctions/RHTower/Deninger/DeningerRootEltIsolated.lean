import GaloisForLFunctions.RHTower.Deninger.DeningerRootEltCentral

/-!
# The adjoined root is isolated

An element whose positive power is a power of the adjoined root commutes with that power.  If the
power is not in the base group the centralizer criterion for factor elements places the element in
the infinite cyclic factor; if it is, the centralizer theorem with that factor exempted does the
same.  Either way the element is a power of the adjoined root, so the cyclic subgroup it generates
is isolated.

* `deningerOfFalse_mem_zpowers` : the cyclic factor is the powers of the adjoined root.
* `deningerRootElt_isolated` : isolation of the adjoined root.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- **The cyclic factor is the set of powers of the adjoined root.** -/
theorem deningerOfFalse_mem_zpowers (x : deningerRootFactor A (ULift.up false)) :
    PushoutI.of (φ := deningerRootMap A a m) (ULift.up false) x ∈
      Subgroup.zpowers (deningerRootElt A a m) := by
  obtain ⟨c, hc⟩ : ∃ c : ℤ, deningerRootGen.{u} ^ c = x := by
    refine ⟨Multiplicative.toAdd (MulEquiv.ulift x), ?_⟩
    apply MulEquiv.ulift.injective
    apply Multiplicative.toAdd.injective
    simp [deningerRootGen]
  refine ⟨c, ?_⟩
  show (deningerRootElt A a m) ^ c = _
  rw [deningerRootElt, ← map_zpow]
  exact congrArg (PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)) hc

/-- **The adjoined root is isolated.** -/
theorem deningerRootElt_isolated (hm : m ≠ 0)
    (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (hcentA : ∀ (x : A) (c : ℤ), c ≠ 0 → x * a ^ c * x⁻¹ = a ^ c → x ∈ Subgroup.zpowers a)
    (hA : ∀ (x y : A) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y)
    (hiso : ∀ (y : A) (n : ℕ), 0 < n → y ^ n ∈ Subgroup.zpowers a → y ∈ Subgroup.zpowers a)
    (htorA : ∀ (x : A) (n : ℕ), 0 < n → x ^ n = 1 → x = 1)
    (y : PushoutI (deningerRootMap A a m)) (n : ℕ) (hn : 0 < n)
    (hy : y ^ n ∈ Subgroup.zpowers (deningerRootElt A a m)) :
    y ∈ Subgroup.zpowers (deningerRootElt A a m) := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerRootMap A a m)
    (deningerRootMap_injective A a m hm ha)
  have hself : ∀ (i : ULift Bool) (z : deningerRootFactor A i) (v : ULift.{u} (Multiplicative ℤ)),
      i ≠ ULift.up false → v ≠ 1 →
      z * deningerRootMap A a m i v * z⁻¹ = deningerRootMap A a m i v →
      z ∈ (deningerRootMap A a m i).range := by
    rintro ⟨b⟩ z v hi hv hz
    cases b
    · exact absurd rfl hi
    · have hne : Multiplicative.toAdd (MulEquiv.ulift v) ≠ 0 := by
        intro hzero
        refine hv ?_
        apply MulEquiv.ulift.injective
        apply Multiplicative.toAdd.injective
        simpa using hzero
      exact (deningerRootMap_true_mem_iff A a m z).2
        (hcentA z (Multiplicative.toAdd (MulEquiv.ulift v)) hne hz)
  obtain ⟨c, hc⟩ := hy
  have hcpow : (deningerRootElt A a m) ^ c = y ^ n := hc
  have hcomm : y * (y ^ n) = (y ^ n) * y := (Commute.refl y).pow_right n
  by_cases hgc : deningerRootGen.{u} ^ c ∈ (deningerRootMap A a m (ULift.up false)).range
  · obtain ⟨k, hk⟩ := hgc
    have h1 : PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)
        (deningerRootMap A a m (ULift.up false) k) = PushoutI.base (deningerRootMap A a m) k :=
      PushoutI.of_apply_eq_base _ _ _
    have h2 : (deningerRootElt A a m) ^ c =
        PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)
          (deningerRootMap A a m (ULift.up false) k) := by
      rw [deningerRootElt, ← map_zpow]
      exact congrArg (PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)) hk.symm
    have hbase : y ^ n = PushoutI.base (deningerRootMap A a m) k := by
      rw [← hcpow, h2, h1]
    by_cases hk1 : k = 1
    · subst hk1
      rw [map_one] at hbase
      have hy1 : y = 1 :=
        deningerRootAdjunction_torsionFree A a m hm ha htorA y n hn hbase
      exact ⟨0, by simp [hy1]⟩
    · obtain ⟨x, hx⟩ := deningerCentralizer_base_one (d := d)
        (deningerRootHcent A a m hm ha hA hiso) (ULift.up false) hself k hk1 y
        (by rw [← hbase]; exact hcomm)
      rw [hx]
      exact deningerOfFalse_mem_zpowers A a m x
  · have hEq : PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)
        (deningerRootGen.{u} ^ c) = y ^ n := by
      rw [← hcpow, deningerRootElt]
      exact map_zpow (PushoutI.of (φ := deningerRootMap A a m) (ULift.up false))
        deningerRootGen.{u} c
    obtain ⟨x, hx⟩ | ⟨x', k, hk⟩ :=
      deningerCentralizer_factor (d := d) (ULift.up false) (deningerRootGen.{u} ^ c) hgc y
        (by rw [hEq]; exact hcomm)
    · rw [hx]
      exact deningerOfFalse_mem_zpowers A a m x
    · refine absurd ⟨k, ?_⟩ hgc
      exact (deningerRootFactorFalse_conj A x'⁻¹ (deningerRootGen.{u} ^ c) _
        (by rw [inv_inv]; exact hk)).symm

end RootAdjunction

end RHTower

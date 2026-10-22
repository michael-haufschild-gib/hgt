import GaloisForLFunctions.RHTower.Deninger.DeningerRootIsolated

/-!
# Conjugation of an isolated element in a group with unique roots

In a group with unique roots no element is conjugate to its own inverse: if `x a x⁻¹ = a⁻¹` then
`x²` commutes with `a`, so `xa` and `x` have the same square and are therefore equal.  Together with
isolation this pins down conjugation of the powers of an isolated element of infinite order: a
conjugate of such a power which is again a power forces the conjugation to fix the element outright.

* `deningerNoInversion` : no element is conjugate to its inverse.
* `deningerConj_zpow_fixes` : conjugation carrying a power of an isolated element to a power fixes
  the element.
-/

namespace RHTower

universe u

/-- **In a group with unique roots no element is conjugate to its inverse.** -/
theorem deningerNoInversion {A : Type u} [Group A]
    (hA : ∀ (x y : A) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y)
    (x a : A) (h : x * a * x⁻¹ = a⁻¹) : a = 1 := by
  have hinv : x * a⁻¹ * x⁻¹ = a := by
    rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group, h, inv_inv]
  have h2 : x * (x * a * x⁻¹) * x⁻¹ = a := by rw [h, hinv]
  have h3 : (x * x) * a * (x * x)⁻¹ = a := by
    rw [show (x * x) * a * (x * x)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ by group]
    exact h2
  have hcomm : (x * x) * a = a * (x * x) := by
    calc (x * x) * a = ((x * x) * a * (x * x)⁻¹) * (x * x) := by group
      _ = a * (x * x) := by rw [h3]
  have hsq : (x * a) * (x * a) = x * x := by
    calc (x * a) * (x * a) = (x * a * x⁻¹) * ((x * x) * a) := by group
      _ = a⁻¹ * (a * (x * x)) := by rw [h, hcomm]
      _ = x * x := by group
  have hxa : x * a = x :=
    hA (x * a) x 2 (by norm_num) (by rw [pow_two, pow_two]; exact hsq)
  simp at hxa
  exact hxa

/-- Conjugation commutes with taking integer powers. -/
theorem deningerConj_zpow_eq {A : Type u} [Group A] (x a : A) (m : ℤ) :
    (x * a * x⁻¹) ^ m = x * a ^ m * x⁻¹ :=
  (map_zpow (MulAut.conj x) a m).symm

/-- A power of an element whose integer power lies in the powers of `a` lies there too. -/
theorem deningerNatAbs_mem_zpowers {A : Type u} [Group A] (a b : A) (c e : ℤ)
    (h : b ^ c = a ^ e) : b ^ c.natAbs ∈ Subgroup.zpowers a := by
  rcases Int.natAbs_eq c with hc | hc
  · refine ⟨e, ?_⟩
    show a ^ e = b ^ c.natAbs
    rw [← h, ← zpow_natCast b c.natAbs, ← hc]
  · refine ⟨-e, ?_⟩
    show a ^ (-e) = b ^ c.natAbs
    rw [zpow_neg, ← h, ← zpow_natCast b c.natAbs,
      show ((c.natAbs : ℤ)) = -c by omega, zpow_neg]

/-- **Conjugation carrying a power of an isolated element to a power fixes the element.** -/
theorem deningerConj_zpow_fixes {A : Type u} [Group A]
    (hA : ∀ (x y : A) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y)
    (a : A) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (hiso : ∀ (y : A) (n : ℕ), 0 < n → y ^ n ∈ Subgroup.zpowers a → y ∈ Subgroup.zpowers a)
    (x : A) (c e : ℤ) (hc : c ≠ 0) (h : x * a ^ c * x⁻¹ = a ^ e) : x * a * x⁻¹ = a := by
  have hane : a ≠ 1 := by
    intro hone
    exact absurd (ha 1 (by rw [hone, zpow_one])) (by norm_num)
  have hbc : (x * a * x⁻¹) ^ c = a ^ e := by rw [deningerConj_zpow_eq, h]
  obtain ⟨s, hs'⟩ : x * a * x⁻¹ ∈ Subgroup.zpowers a :=
    hiso _ c.natAbs (by omega) (deningerNatAbs_mem_zpowers a _ c e hbc)
  have hs : a ^ s = x * a * x⁻¹ := hs'
  have hsne : s ≠ 0 := by
    intro hzero
    rw [hzero, zpow_zero] at hs
    exact hane (by simpa using hs.symm)
  have hy : (x⁻¹ * a * x) ^ s = a := by
    rw [show x⁻¹ * a * x = x⁻¹ * a * x⁻¹⁻¹ by group, deningerConj_zpow_eq, hs]
    group
  obtain ⟨r, hr'⟩ : x⁻¹ * a * x ∈ Subgroup.zpowers a :=
    hiso _ s.natAbs (by omega) (deningerNatAbs_mem_zpowers a _ s 1 (by rw [hy, zpow_one]))
  have hr : a ^ r = x⁻¹ * a * x := hr'
  have hrs : r * s = 1 := by
    have h1 : a ^ (r * s) = a ^ (1 : ℤ) := by
      rw [zpow_mul, hr, hy, zpow_one]
    have h2 : a ^ (r * s - 1) = 1 := by
      rw [sub_eq_add_neg, zpow_add, h1, zpow_neg, zpow_one, mul_inv_cancel]
    have := ha _ h2
    omega
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.1 hrs with ⟨-, hs1⟩ | ⟨-, hs1⟩
  · rw [← hs, hs1, zpow_one]
  · exfalso
    refine hane (deningerNoInversion hA x a ?_)
    rw [← hs, hs1]
    simp

end RHTower

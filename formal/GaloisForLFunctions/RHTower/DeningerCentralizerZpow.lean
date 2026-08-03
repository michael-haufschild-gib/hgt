import GaloisForLFunctions.RHTower.DeningerRGroupConjugation

/-!
# Centralizers of powers in a group with unique roots

In a group with unique roots an element centralizing a nonzero power of `a` centralizes `a` itself:
conjugation is an automorphism, so the conjugate of `a` has the same power as `a`, and unique roots
identify them.  So the condition that the centralizer of every nontrivial power of `a` lie in the
cyclic subgroup it generates reduces to the same condition for `a`.

* `deningerZpow_eq_of_pow_eq` : unique roots for integer exponents.
* `deningerCentralizer_zpow_eq` : centralizing a power is centralizing the element.
* `deningerCentralizer_zpow_subset` : the self-centralizing condition, reduced to the element.
-/

namespace RHTower

universe u

variable {A : Type u} [Group A]

/-- **Unique roots for integer exponents.** -/
theorem deningerZpow_eq_of_pow_eq
    (hA : ∀ (x y : A) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y)
    (b a : A) (c : ℤ) (hc : c ≠ 0) (h : b ^ c = a ^ c) : b = a := by
  have hpos : 0 < c.natAbs := by omega
  rcases Int.natAbs_eq c with hc' | hc'
  · refine hA b a c.natAbs hpos ?_
    rw [← zpow_natCast b c.natAbs, ← zpow_natCast a c.natAbs, ← hc']
    exact h
  · refine hA b a c.natAbs hpos ?_
    have hb : b ^ ((c.natAbs : ℤ)) = (b ^ c)⁻¹ := by
      rw [show ((c.natAbs : ℤ)) = -c by omega, zpow_neg]
    have hb' : a ^ ((c.natAbs : ℤ)) = (a ^ c)⁻¹ := by
      rw [show ((c.natAbs : ℤ)) = -c by omega, zpow_neg]
    rw [← zpow_natCast b c.natAbs, ← zpow_natCast a c.natAbs, hb, hb', h]

/-- **Centralizing a nonzero power is centralizing the element.** -/
theorem deningerCentralizer_zpow_eq
    (hA : ∀ (x y : A) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y)
    (a x : A) (c : ℤ) (hc : c ≠ 0) (h : x * a ^ c * x⁻¹ = a ^ c) : x * a * x⁻¹ = a := by
  refine deningerZpow_eq_of_pow_eq hA _ a c hc ?_
  rw [deningerConj_zpow_eq, h]

/-- **The self-centralizing condition, reduced to the element.** -/
theorem deningerCentralizer_zpow_subset
    (hA : ∀ (x y : A) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y) (a : A)
    (hC : ∀ x : A, x * a * x⁻¹ = a → x ∈ Subgroup.zpowers a)
    (x : A) (c : ℤ) (hc : c ≠ 0) (h : x * a ^ c * x⁻¹ = a ^ c) : x ∈ Subgroup.zpowers a :=
  hC x (deningerCentralizer_zpow_eq hA a x c hc h)

end RHTower

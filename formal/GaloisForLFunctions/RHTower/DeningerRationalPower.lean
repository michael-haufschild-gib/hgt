import GaloisForLFunctions.RHTower.DeningerBaumslagGeneration

/-!
# Rational powers in a group with unique roots

In a group with unique roots the roots of a fixed element are all powers of a common deeper root:
the `(a+1)(b+1)`-st root, raised to `b+1`, is the `(a+1)-st` root, because both are `(a+1)`-st roots
of the same element.  Consequently `(root_d h) ^ n` depends only on the rational `n/d`, and `h`
carries a well-defined action of `ℚ`.

This is the classical statement that a group with unique roots is a `ℚ`-powered group, in the form
needed for one element at a time.

* `deningerRoot_pow_root` : the compatibility of roots.
* `deningerRootPow_congr` : `(root_d h) ^ n` depends only on `n/d`.
* `deningerRatPow` : the resulting homomorphism `Multiplicative ℚ →* H`.
-/

namespace RHTower

section RationalPower

variable {H : Type*} [Group H] (hH : DeningerUniquelyDivisible H) (h : H)

/-- **Roots refine**: the `(a+1)(b+1)`-st root, raised to `b+1`, is the `(a+1)`-st root. -/
theorem deningerRoot_pow_root (a b : ℕ) :
    deningerRoot hH (a * b + a + b) h ^ (b + 1) = deningerRoot hH a h := by
  refine deningerRoot_unique hH a ?_
  rw [← pow_mul]
  have hab : (b + 1) * (a + 1) = a * b + a + b + 1 := by ring
  rw [hab]
  exact deningerRoot_pow hH _ h

/-- The rational power `h ^ (n / (d+1))`. -/
noncomputable def deningerRootPow (n : ℤ) (d : ℕ) : H := deningerRoot hH d h ^ n

/-- **The rational power depends only on the rational number.** -/
theorem deningerRootPow_congr {n n' : ℤ} {d d' : ℕ}
    (hnd : n * (d' + 1 : ℤ) = n' * (d + 1 : ℤ)) :
    deningerRootPow hH h n d = deningerRootPow hH h n' d' := by
  have h1 : deningerRoot hH (d * d' + d + d') h ^ (d' + 1) = deningerRoot hH d h :=
    deningerRoot_pow_root hH h d d'
  have h2 : deningerRoot hH (d * d' + d + d') h ^ (d + 1) = deningerRoot hH d' h := by
    have := deningerRoot_pow_root hH h d' d
    rwa [show d' * d + d' + d = d * d' + d + d' by ring] at this
  show deningerRoot hH d h ^ n = deningerRoot hH d' h ^ n'
  rw [← h1, ← h2, ← zpow_natCast (deningerRoot hH (d * d' + d + d') h) (d' + 1),
    ← zpow_natCast (deningerRoot hH (d * d' + d + d') h) (d + 1), ← zpow_mul, ← zpow_mul]
  congr 1
  push_cast
  linarith [hnd]

/-- **The rational power operation** on a fixed element of a group with unique roots. -/
noncomputable def deningerRatPow : Multiplicative ℚ →* H where
  toFun q := deningerRootPow hH h (Multiplicative.toAdd q).num
    ((Multiplicative.toAdd q).den - 1)
  map_one' := by
    show deningerRootPow hH h (0 : ℚ).num ((0 : ℚ).den - 1) = 1
    show deningerRoot hH ((0 : ℚ).den - 1) h ^ (0 : ℚ).num = 1
    norm_num
  map_mul' q₁ q₂ := by
    set a := Multiplicative.toAdd q₁ with ha
    set b := Multiplicative.toAdd q₂ with hb
    have hda : ((a.den - 1 : ℕ) : ℤ) + 1 = (a.den : ℤ) := by
      have := a.pos
      omega
    have hdb : ((b.den - 1 : ℕ) : ℤ) + 1 = (b.den : ℤ) := by
      have := b.pos
      omega
    have hdab : (((a + b).den - 1 : ℕ) : ℤ) + 1 = ((a + b).den : ℤ) := by
      have := (a + b).pos
      omega
    have hstep₁ : deningerRootPow hH h a.num (a.den - 1) =
        deningerRootPow hH h (a.num * b.den) (a.den * b.den - 1) := by
      refine deningerRootPow_congr hH h ?_
      have hd : ((a.den * b.den - 1 : ℕ) : ℤ) + 1 = (a.den : ℤ) * (b.den : ℤ) := by
        have h1 := a.pos
        have h2 := b.pos
        have : 1 ≤ a.den * b.den := Nat.one_le_iff_ne_zero.2 (by positivity)
        push_cast [Nat.cast_sub this]
        ring
      rw [hd, hda]
      ring
    have hstep₂ : deningerRootPow hH h b.num (b.den - 1) =
        deningerRootPow hH h (b.num * a.den) (a.den * b.den - 1) := by
      refine deningerRootPow_congr hH h ?_
      have hd : ((a.den * b.den - 1 : ℕ) : ℤ) + 1 = (a.den : ℤ) * (b.den : ℤ) := by
        have : 1 ≤ a.den * b.den := Nat.one_le_iff_ne_zero.2 (by positivity)
        push_cast [Nat.cast_sub this]
        ring
      rw [hd, hdb]
      ring
    have hstep₃ : deningerRootPow hH h (a + b).num ((a + b).den - 1) =
        deningerRootPow hH h (a.num * b.den + b.num * a.den) (a.den * b.den - 1) := by
      refine deningerRootPow_congr hH h ?_
      have hd : ((a.den * b.den - 1 : ℕ) : ℤ) + 1 = (a.den : ℤ) * (b.den : ℤ) := by
        have : 1 ≤ a.den * b.den := Nat.one_le_iff_ne_zero.2 (by positivity)
        push_cast [Nat.cast_sub this]
        ring
      rw [hd, hdab]
      have hnum : ((a + b).num : ℚ) * ((a.den : ℚ) * (b.den : ℚ)) =
          ((a.num * b.den + b.num * a.den : ℤ) : ℚ) * ((a + b).den : ℚ) := by
        have hA : (a.num : ℚ) = a * a.den := by
          have hnd := Rat.num_div_den a
          have hdne : ((a.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 a.den_nz
          field_simp at hnd
          exact hnd.trans (mul_comm _ _)
        have hB : (b.num : ℚ) = b * b.den := by
          have hnd := Rat.num_div_den b
          have hdne : ((b.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 b.den_nz
          field_simp at hnd
          exact hnd.trans (mul_comm _ _)
        have hC : ((a + b).num : ℚ) = (a + b) * (a + b).den := by
          have hnd := Rat.num_div_den (a + b)
          have hdne : (((a + b).den : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (a + b).den_nz
          field_simp at hnd
          exact hnd
        push_cast
        rw [hA, hB, hC]
        ring
      exact_mod_cast hnum
    show deningerRootPow hH h (a + b).num ((a + b).den - 1) =
      deningerRootPow hH h a.num (a.den - 1) * deningerRootPow hH h b.num (b.den - 1)
    rw [hstep₁, hstep₂, hstep₃]
    show deningerRoot hH (a.den * b.den - 1) h ^ (a.num * b.den + b.num * a.den) =
      deningerRoot hH (a.den * b.den - 1) h ^ (a.num * b.den) *
        deningerRoot hH (a.den * b.den - 1) h ^ (b.num * a.den)
    rw [← zpow_add]

end RationalPower

end RHTower

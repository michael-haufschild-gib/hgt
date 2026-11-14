import GaloisForLFunctions.RHTower.Schanuel.SchanuelAffineCharacterNormalForm
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic.Ring

/-!
# Primitive integral normal forms for rank-one binary forms

An integral symmetric binary form has determinant zero exactly when it is an
integer multiple of the square of a primitive integral linear form. Bézout
coefficients recover the integer multiplier without a divisibility premise.
The primitive row then uses the existing determinant-one isogeny completion.
This is the integral normalization mechanism of Du, Lemma 6.2.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.RHTower

/-- Every singular integral binary form is an integral square of a primitive row.
The zero form is included, so no nonvanishing or rank premise is required. -/
theorem binary_rank_one_iff (x y z : ℤ) :
    y ^ 2 = x * z ↔ ∃ t u v : ℤ, Int.gcd u v = 1 ∧
      x = t * u ^ 2 ∧ y = t * u * v ∧ z = t * v ^ 2 := by
  constructor
  · intro hdet
    by_cases hx0 : x = 0
    · have hy0 : y = 0 := sq_eq_zero_iff.mp (by rw [hdet, hx0, zero_mul])
      refine ⟨z, 0, 1, ?_, ?_, ?_, ?_⟩ <;> simp [hx0, hy0]
    · obtain ⟨u, v, huv, hx, hy⟩ :=
        Int.exists_gcd_one (Int.gcd_pos_of_ne_zero_left y hx0)
      let g : ℤ := Int.gcd x y
      change x = u * g at hx
      change y = v * g at hy
      have hg : g ≠ 0 := by
        intro hg0
        exact hx0 (by rw [hx, hg0, mul_zero])
      have hu : u ≠ 0 := by
        intro hu0
        exact hx0 (by rw [hx, hu0, zero_mul])
      have huc : u * z = v ^ 2 * g := by
        apply mul_right_cancel₀ hg
        calc
          u * z * g = (u * g) * z := by ring
          _ = x * z := by rw [← hx]
          _ = y ^ 2 := hdet.symm
          _ = (v ^ 2 * g) * g := by rw [hy]; ring
      let A := Int.gcdA u v
      let B := Int.gcdB u v
      have hbez : u * A + v * B = 1 := by
        have h := Int.gcd_eq_gcd_ab u v
        rw [huv] at h
        exact h.symm
      let t := A ^ 2 * x + 2 * A * B * y + B ^ 2 * z
      have ht : u * t = g := by
        calc
          u * t = g * (u * A + v * B) ^ 2 + B ^ 2 * (u * z - v ^ 2 * g) := by
            dsimp [t]
            rw [hx, hy]
            ring
          _ = g := by rw [hbez, huc, sub_self, mul_zero, add_zero, one_pow, mul_one]
      refine ⟨t, u, v, huv, ?_, ?_, ?_⟩
      · rw [hx, ← ht]
        ring
      · rw [hy, ← ht]
        ring
      · apply mul_left_cancel₀ hu
        rw [huc, ← ht]
        ring
  · rintro ⟨t, u, v, _, rfl, rfl, rfl⟩
    ring

/-- Half-integral singular forms are automatically integral and have the same primitive factorization. -/
theorem half_integral_rank_one_iff (x r z : ℤ) :
    r ^ 2 = 4 * x * z ↔ ∃ t u v : ℤ, Int.gcd u v = 1 ∧
      x = t * u ^ 2 ∧ r = 2 * t * u * v ∧ z = t * v ^ 2 := by
  constructor
  · intro hdet
    have he : Even (r ^ 2) := ⟨2 * x * z, by rw [hdet]; ring⟩
    obtain ⟨y, hy⟩ := (Int.even_pow.mp he).1
    have hsmall : y ^ 2 = x * z := by
      rw [hy] at hdet
      nlinarith only [hdet]
    obtain ⟨t, u, v, huv, hx, hy', hz⟩ := (binary_rank_one_iff x y z).mp hsmall
    refine ⟨t, u, v, huv, hx, ?_, hz⟩
    rw [hy, hy']
    ring
  · rintro ⟨t, u, v, _, rfl, rfl, rfl⟩
    ring

/-- Singular binary forms factor through a primitive character with a determinant-one completion. -/
theorem binary_rank_one_isogeny_normal_form (x y z : ℤ) :
    y ^ 2 = x * z ↔ ∃ (t u v : ℤ) (h : Int.gcd u v = 1),
      x = t * u ^ 2 ∧ y = t * u * v ∧ z = t * v ^ 2 ∧
      (primitiveIntegralIsogenyMatrix2 u v h).a *
          (primitiveIntegralIsogenyMatrix2 u v h).d -
        (primitiveIntegralIsogenyMatrix2 u v h).b *
          (primitiveIntegralIsogenyMatrix2 u v h).c = 1 ∧
      ∀ p q : ℂ, (x : ℂ) * p ^ 2 + 2 * (y : ℂ) * p * q + (z : ℂ) * q ^ 2 =
        (t : ℂ) * (integralIsogenyAdditiveCoordinates ![p, q]
          (primitiveIntegralIsogenyMatrix2 u v h) 0) ^ 2 := by
  rw [binary_rank_one_iff]
  constructor
  · rintro ⟨t, u, v, h, hx, hy, hz⟩
    refine ⟨t, u, v, h, hx, hy, hz, ?_, ?_⟩
    · change u * Int.gcdA u v - v * (-Int.gcdB u v) = 1
      have hb := Int.gcd_eq_gcd_ab u v
      rw [h] at hb
      calc
        _ = u * Int.gcdA u v + v * Int.gcdB u v := by ring
        _ = 1 := hb.symm
    · intro p q
      rw [hx, hy, hz]
      simp only [integralIsogenyAdditiveCoordinates, if_pos rfl,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        primitiveIntegralIsogenyMatrix2]
      push_cast
      ring
  · rintro ⟨t, u, v, h, hx, hy, hz, _, _⟩
    exact ⟨t, u, v, h, hx, hy, hz⟩

#print axioms binary_rank_one_iff
#print axioms half_integral_rank_one_iff
#print axioms binary_rank_one_isogeny_normal_form

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

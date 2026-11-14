import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Operations

/-!
# Two branches and their contact ideal

Values on the branches `X = 0` and `X = a` come from one polynomial exactly
when their difference is divisible by `a`. The conductor in the product
ring is the contact ideal on each factor. This is the two smooth branch
case of the conductor/contact decomposition in Du, Theorem 8.12.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {R : Type*} [CommRing R]

/-- The exact integral interpolation condition, including coincident branches. -/
theorem twoBranch_interpolation_iff (a x y : R) :
    (∃ p : R[X], p.eval 0 = x ∧ p.eval a = y) ↔ a ∣ y - x := by
  constructor
  · rintro ⟨p, hx, hy⟩
    simpa only [sub_zero, hx, hy] using Polynomial.sub_dvd_eval_sub a 0 p
  · rintro ⟨b, hb⟩
    refine ⟨C x + C b * X, ?_, ?_⟩
    · simp only [eval_add, eval_C, eval_mul, eval_X, mul_zero, add_zero]
    · simp only [eval_add, eval_C, eval_mul, eval_X]
      calc
        x + b * a = x + a * b := by rw [mul_comm b a]
        _ = y := by rw [← hb]; ring

/-- The conductor of the congruence order is the contact ideal in both factors. -/
theorem product_contact_conductor_iff (I : Ideal R) (z : R × R) :
    (∀ w : R × R, (z * w).1 - (z * w).2 ∈ I) ↔ z.1 ∈ I ∧ z.2 ∈ I := by
  constructor
  · intro h
    constructor
    · simpa only [Prod.fst_mul, Prod.snd_mul, mul_one, mul_zero, sub_zero]
        using h (1, 0)
    · have hn : -z.2 ∈ I := by
        simpa only [Prod.fst_mul, Prod.snd_mul, mul_one, mul_zero, zero_sub]
          using h (0, 1)
      simpa only [neg_neg] using I.neg_mem hn
  · rintro ⟨hx, hy⟩ w
    exact I.sub_mem (I.mul_mem_right w.1 hx) (I.mul_mem_right w.2 hy)

/-- Multiplication by a pair sends every pair in the product ring into the polynomial order
exactly when both coordinates vanish to the contact order. -/
theorem twoBranch_conductor_iff (a x y : R) :
    (∀ u v : R, ∃ p : R[X], p.eval 0 = x * u ∧ p.eval a = y * v) ↔
      a ∣ x ∧ a ∣ y := by
  simp only [twoBranch_interpolation_iff]
  constructor
  · intro h
    constructor
    · simpa only [mul_one, mul_zero, zero_sub, dvd_neg] using h 1 0
    · simpa only [mul_one, mul_zero, sub_zero] using h 0 1
  · rintro ⟨hx, hy⟩ u v
    exact dvd_sub (dvd_mul_of_dvd_left hy v) (dvd_mul_of_dvd_left hx u)

#print axioms twoBranch_interpolation_iff
#print axioms product_contact_conductor_iff
#print axioms twoBranch_conductor_iff

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

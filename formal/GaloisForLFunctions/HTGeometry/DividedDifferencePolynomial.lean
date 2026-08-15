import Mathlib

/-!
# The divided difference of a polynomial

The difference `P(ζ) − P(z)` of a polynomial of degree at most `d`, written in coefficients, is
divisible by `ζ − z`, and the quotient is a polynomial of degree at most `d − 1` in `z` whose
coefficients are polynomials in `ζ`.  This is the algebraic content of the remainder in
Weierstrass' division theorem: dividing a Cauchy kernel by a monic polynomial of degree `d` leaves
a remainder of degree below `d`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

/-- The coefficient of `z ^ k` in the divided difference of a polynomial with coefficients `p` and
degree at most `d`. -/
def dividedDifferenceCoeff {R : Type*} [CommRing R] (d : ℕ) (p : ℕ → R) (ζ : R) (k : ℕ) : R :=
  ∑ j ∈ Finset.Ico (k + 1) (d + 1), p j * ζ ^ (j - 1 - k)

theorem pow_sub_pow_eq_mul {R : Type*} [CommRing R] (ζ z : R) (j : ℕ) :
    ζ ^ j - z ^ j = (ζ - z) * ∑ k ∈ Finset.range j, ζ ^ (j - 1 - k) * z ^ k := by
  have hrefl : (∑ k ∈ Finset.range j, ζ ^ (j - 1 - k) * z ^ k)
      = ∑ i ∈ Finset.range j, ζ ^ i * z ^ (j - 1 - i) := by
    rw [← Finset.sum_range_reflect (fun i => ζ ^ i * z ^ (j - 1 - i)) j]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    congr 2
    omega
  rw [hrefl, mul_comm]
  exact (geom_sum₂_mul ζ z j).symm

/-- **The divided difference of a polynomial.** -/
theorem poly_sub_eq_mul_dividedDifference {R : Type*} [CommRing R] (d : ℕ) (p : ℕ → R) (ζ z : R) :
    (∑ j ∈ Finset.range (d + 1), p j * ζ ^ j) - (∑ j ∈ Finset.range (d + 1), p j * z ^ j)
      = (ζ - z) * ∑ k ∈ Finset.range d, dividedDifferenceCoeff d p ζ k * z ^ k := by
  classical
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ Finset.range (d + 1), p j * ζ ^ j - p j * z ^ j
      = (ζ - z) * ∑ k ∈ Finset.range j, p j * ζ ^ (j - 1 - k) * z ^ k := by
    intro j _
    have hpull : ∑ k ∈ Finset.range j, p j * ζ ^ (j - 1 - k) * z ^ k
        = p j * ∑ k ∈ Finset.range j, ζ ^ (j - 1 - k) * z ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [← mul_sub, pow_sub_pow_eq_mul, hpull]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm' (t' := Finset.range d) (s' := fun k => Finset.Ico (k + 1) (d + 1))
    (by
      intro j k
      simp only [Finset.mem_range, Finset.mem_Ico]
      omega)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dividedDifferenceCoeff, Finset.sum_mul]

end GaloisForLFunctions.HTGeometry

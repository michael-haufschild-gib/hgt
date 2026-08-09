import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The divided difference of a polynomial

The difference of a polynomial evaluated at two points is divisible by the difference of the
points, and the quotient is again a polynomial in each of them, of degree one less.  Written out in
the coefficients, the quotient's coefficient of `z^l` is a truncated tail of the original
coefficients evaluated at the other point.

This is the algebraic step of Weierstrass' division theorem: the remainder is manufactured from
this quotient, and its degree bound in the distinguished variable is exactly what makes the
remainder a polynomial of degree below that of the divisor.

* `GaloisForLFunctions.HTGeometry.sum_pow_sub_sum_pow_eq`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **The divided difference of a polynomial, in coordinates.** -/
theorem sum_pow_sub_sum_pow_eq (a : ℕ → ℂ) (K : ℕ) (ζ z : ℂ) :
    (∑ j ∈ range K, a j * ζ ^ j) - (∑ j ∈ range K, a j * z ^ j)
      = (∑ l ∈ range K, (∑ j ∈ Ico (l + 1) K, a j * ζ ^ (j - 1 - l)) * z ^ l) * (ζ - z) := by
  classical
  have hstep : ∀ j : ℕ, a j * ζ ^ j - a j * z ^ j
      = (∑ i ∈ range j, a j * ζ ^ i * z ^ (j - 1 - i)) * (ζ - z) := by
    intro j
    have hgeom := geom_sum₂_mul ζ z j
    calc a j * ζ ^ j - a j * z ^ j = a j * (ζ ^ j - z ^ j) := by ring
      _ = a j * ((∑ i ∈ range j, ζ ^ i * z ^ (j - 1 - i)) * (ζ - z)) := by rw [hgeom]
      _ = (∑ i ∈ range j, a j * ζ ^ i * z ^ (j - 1 - i)) * (ζ - z) := by
          have hdist : (∑ i ∈ range j, a j * ζ ^ i * z ^ (j - 1 - i))
              = a j * ∑ i ∈ range j, ζ ^ i * z ^ (j - 1 - i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
          rw [hdist]
          ring
  have hleft : (∑ j ∈ range K, a j * ζ ^ j) - (∑ j ∈ range K, a j * z ^ j)
      = (∑ j ∈ range K, ∑ i ∈ range j, a j * ζ ^ i * z ^ (j - 1 - i)) * (ζ - z) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hstep j
  have hreflect : ∀ j : ℕ, (∑ i ∈ range j, a j * ζ ^ i * z ^ (j - 1 - i))
      = ∑ l ∈ range j, a j * ζ ^ (j - 1 - l) * z ^ l := by
    intro j
    rw [← Finset.sum_range_reflect (fun i => a j * ζ ^ i * z ^ (j - 1 - i)) j]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l < j := Finset.mem_range.1 hl
    have hindex : j - 1 - (j - 1 - l) = l := by omega
    rw [hindex]
  have hswap : (∑ j ∈ range K, ∑ l ∈ range j, a j * ζ ^ (j - 1 - l) * z ^ l)
      = ∑ l ∈ range K, ∑ j ∈ Ico (l + 1) K, a j * ζ ^ (j - 1 - l) * z ^ l := by
    refine Finset.sum_comm' ?_
    intro j l
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hleft]
  refine congrArg (· * (ζ - z)) ?_
  rw [Finset.sum_congr rfl fun j _ => hreflect j, hswap]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]

end GaloisForLFunctions.HTGeometry

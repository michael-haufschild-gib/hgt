import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResidueFloorSum

/-!
# Multiplication floor sums and their vanishing threshold

Summing Euclidean division and the uniform multiplication-residue count
evaluates `∑ i < N, Ri/N`. For `N ≥ 2`, this sum vanishes exactly when
`R ≤ 1`. These sums count the branch factors removed from an integral basis.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Finset

/-- The complete multiplication floor sum, in a subtraction-free identity. -/
theorem two_mul_sum_mul_div_add (N R : ℕ) (hN : 0 < N) :
    2 * (∑ i ∈ range N, R * i / N) + N = R * (N - 1) + Nat.gcd N R := by
  have hg : Nat.gcd N R ≤ N := Nat.le_of_dvd hN (Nat.gcd_dvd_left N R)
  have hdivision : N * (∑ i ∈ range N, R * i / N) + (∑ i ∈ range N, R * i % N) =
      R * (∑ i ∈ range N, i) := by
    rw [mul_sum, ← sum_add_distrib]
    simp only [Nat.div_add_mod]
    rw [mul_sum]
  have hsplit : N * N = N * (N - Nat.gcd N R) + N * Nat.gcd N R := by
    rw [← mul_add, Nat.sub_add_cancel hg]
  apply Nat.eq_of_mul_eq_mul_left hN
  calc
    N * (2 * (∑ i ∈ range N, R * i / N) + N) =
        2 * (N * (∑ i ∈ range N, R * i / N)) + N * N := by ring
    _ = 2 * (N * (∑ i ∈ range N, R * i / N)) +
        (N * (N - Nat.gcd N R) + N * Nat.gcd N R) := by rw [hsplit]
    _ = 2 * (N * (∑ i ∈ range N, R * i / N)) +
        (2 * (∑ i ∈ range N, R * i % N) + N * Nat.gcd N R) := by
      rw [two_mul_sum_mul_mod N R hN]
    _ = 2 * (N * (∑ i ∈ range N, R * i / N) +
        (∑ i ∈ range N, R * i % N)) + N * Nat.gcd N R := by ring
    _ = 2 * (R * (∑ i ∈ range N, i)) + N * Nat.gcd N R := by rw [hdivision]
    _ = R * ((∑ i ∈ range N, i) * 2) + N * Nat.gcd N R := by ring
    _ = R * (N * (N - 1)) + N * Nat.gcd N R := by rw [sum_range_id_mul_two]
    _ = N * (R * (N - 1) + Nat.gcd N R) := by ring

/-- No branch power is removed precisely when its exponent is at most one. -/
theorem sum_mul_div_eq_zero_iff (N R : ℕ) (hN : 2 ≤ N) :
    (∑ i ∈ range N, R * i / N) = 0 ↔ R ≤ 1 := by
  constructor
  · intro hz
    have h := two_mul_sum_mul_div_add N R (by omega)
    rw [hz, mul_zero, zero_add] at h
    have hg : 1 ≤ Nat.gcd N R := Nat.gcd_pos_of_pos_left R (by omega)
    by_contra hR
    have hR2 : 2 ≤ R := by omega
    have hmul := Nat.mul_le_mul_right (N - 1) hR2
    omega
  · intro hR
    have h : R = 0 ∨ R = 1 := by omega
    rcases h with rfl | rfl
    · simp only [zero_mul, Nat.zero_div, sum_const_zero]
    · apply sum_eq_zero
      intro i hi
      simpa only [one_mul] using Nat.div_eq_of_lt (mem_range.mp hi)

#print axioms two_mul_sum_mul_div_add
#print axioms sum_mul_div_eq_zero_iff

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

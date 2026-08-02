import GaloisForLFunctions.HTGeometry.PostcriticalNotRational

/-!
# The coefficient recurrence of a truncated inverse pair

A pair of polynomials whose product is one over a horizon satisfies, in every degree below that
horizon, the convolution identity of an inverse pair:

`∑_(i ≤ k) Z_i W_(k-i)  =  1` for `k = 0` and `0` otherwise.

In particular the constant terms are inverse to one another, and every later reciprocal coefficient
is determined by the earlier ones together with the coefficients of the jet.  This is what lets a
specialisation of the generic jet be recognised on the reciprocal side: both sides satisfy the same
recursion from the same initial value.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

/-- **The convolution identity below the horizon.** -/
theorem coeff_convolution_of_dvd {L : ℕ} {Z W : S[X]}
    (h : (X : S[X]) ^ (L + 1) ∣ Z * W - 1) {k : ℕ} (hk : k ≤ L) :
    ∑ i ∈ Finset.range (k + 1), Z.coeff i * W.coeff (k - i) = if k = 0 then 1 else 0 := by
  rw [Polynomial.X_pow_dvd_iff] at h
  have hc := h k (by omega)
  rw [Polynomial.coeff_sub, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Polynomial.coeff_one, sub_eq_zero] at hc
  exact hc

/-- **The constant terms of a truncated inverse pair are inverse.** -/
theorem coeff_zero_mul_of_dvd {L : ℕ} {Z W : S[X]}
    (h : (X : S[X]) ^ (L + 1) ∣ Z * W - 1) :
    Z.coeff 0 * W.coeff 0 = 1 := by
  have := coeff_convolution_of_dvd h (k := 0) (by omega)
  simpa using this

/-- **The recurrence for the later reciprocal coefficients.** -/
theorem coeff_zero_mul_coeff_of_dvd {L : ℕ} {Z W : S[X]}
    (h : (X : S[X]) ^ (L + 1) ∣ Z * W - 1) {k : ℕ} (hk : k ≤ L) (hk0 : 0 < k) :
    Z.coeff 0 * W.coeff k
      = -∑ i ∈ Finset.range k, Z.coeff (i + 1) * W.coeff (k - (i + 1)) := by
  have hconv := coeff_convolution_of_dvd h hk
  rw [if_neg (by omega)] at hconv
  have hsplit : ∑ i ∈ Finset.range (k + 1), Z.coeff i * W.coeff (k - i)
      = Z.coeff 0 * W.coeff k + ∑ i ∈ Finset.range k, Z.coeff (i + 1) * W.coeff (k - (i + 1)) := by
    exact (Finset.sum_range_succ' _ _).trans (add_comm _ _)
  rw [hsplit] at hconv
  linear_combination hconv

end GaloisForLFunctions.HTGeometry

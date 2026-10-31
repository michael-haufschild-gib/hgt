import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentCollapse

/-!
# Polynomial quadrature away from the origin

Normalized finite-difference weights reproduce evaluation at zero using only nonzero
integer nodes. Rescaling those nodes preserves every polynomial moment below the order.
-/

open Polynomial Finset Complex
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Finite-difference weights after solving for the omitted origin value. -/
def originQuadratureWeight (n : ℕ) (i : Fin n) : ℂ :=
  -((-1 : ℂ) ^ n)⁻¹ *
    ((-1 : ℂ) ^ (n - (i.val + 1)) * (n.choose (i.val + 1) : ℂ))

/-- All quadrature weights are real. -/
theorem conj_originQuadratureWeight (n : ℕ) (i : Fin n) :
    starRingEnd ℂ (originQuadratureWeight n i) = originQuadratureWeight n i := by
  simp only [originQuadratureWeight, map_mul, map_neg, map_inv₀, map_pow,
    map_one, map_natCast]

private theorem binomial_polynomial_sum_eq_zero {n : ℕ} (P : ℂ[X])
    (hP : P.natDegree < n) (x : ℂ) :
    (∑ k ∈ range (n + 1), ((-1 : ℂ) ^ (n - k) * (n.choose k : ℂ)) *
      P.eval ((k : ℂ) * x)) = 0 := by
  simp_rw [Polynomial.eval_eq_sum_range' hP, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  calc
    _ = (P.coeff j * x ^ j) *
        ∑ k ∈ range (n + 1), ((-1 : ℂ) ^ (n - k) * (n.choose k : ℂ)) * (k : ℂ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_pow]
      ring
    _ = 0 := by
      rw [alternating_binomial_sum_pow_eq_zero (Finset.mem_range.mp hj), mul_zero]

/-- Rescaled nonzero integer nodes reproduce polynomial evaluation at the origin. -/
theorem originQuadrature_eval {n : ℕ} (P : ℂ[X]) (hP : P.natDegree < n) (x : ℂ) :
    (∑ i : Fin n, originQuadratureWeight n i * P.eval (((i.val + 1 : ℕ) : ℂ) * x)) =
      P.eval 0 := by
  have h := binomial_polynomial_sum_eq_zero P hP x
  rw [Finset.sum_range, Fin.sum_univ_succ] at h
  simp only [Fin.val_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one, Nat.cast_zero, zero_mul, Fin.val_succ] at h
  have htail := eq_neg_of_add_eq_zero_right h
  have hn : (-1 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  calc
    _ = -((-1 : ℂ) ^ n)⁻¹ * ∑ i : Fin n,
        ((-1 : ℂ) ^ (n - (i.val + 1)) * (n.choose (i.val + 1) : ℂ)) *
          P.eval (((i.val + 1 : ℕ) : ℂ) * x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [originQuadratureWeight, mul_assoc]
    _ = P.eval 0 := by
      rw [htail]
      field_simp [hn]

/-- Translating the polynomial shifts the point reproduced by quadrature. -/
theorem originQuadrature_eval_shifted {n : ℕ} (P : ℂ[X]) (hP : P.natDegree < n)
    (β x : ℂ) :
    (∑ i : Fin n, originQuadratureWeight n i *
      P.eval (((i.val + 1 : ℕ) : ℂ) * x + β)) = P.eval β := by
  have hdeg : (P.comp (X + C β)).natDegree < n := by
    simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using hP
  simpa only [eval_comp, eval_add, eval_X, eval_C, zero_add] using
    originQuadrature_eval (P.comp (X + C β)) hdeg x

/-- The total quadrature weight is one. -/
theorem sum_originQuadratureWeight {n : ℕ} (hn : 0 < n) :
    ∑ i : Fin n, originQuadratureWeight n i = 1 := by
  have h := originQuadrature_eval (1 : ℂ[X]) (by simpa only [natDegree_one] using hn) (1 : ℂ)
  simpa only [eval_one, mul_one] using h

#print axioms originQuadrature_eval
#print axioms sum_originQuadratureWeight
end GaloisForLFunctions.BiarithmeticGeometry

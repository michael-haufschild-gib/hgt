import GaloisForLFunctions.HTGeometry.DirectionalVandermondeQuantitativePhaseJet
import Mathlib.Algebra.Order.Chebyshev

/-!
# Coefficient control by complete polynomial samples

The adjugate identity controls every coefficient by all sample values. The
Vandermonde determinant is retained, so the estimate remains unconditional at
colliding nodes and gives a quantitative lower bound away from collisions.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators

def polynomialSample {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ j, a j * z ^ (j : ℕ)

def polynomialSamplingCap {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  n.factorial * (phaseFrequencyScale z ^ (n - 1)) ^ n

/-- Determinant-weighted coefficient control retains every sample cross term. -/
theorem polynomialSample_coefficient_bound {n : ℕ} (z a : Fin n → ℂ) (j : Fin n) :
    ‖(Matrix.vandermonde z).det‖ * ‖a j‖ ≤
      polynomialSamplingCap z * ∑ i, ‖polynomialSample a (z i)‖ := by
  classical
  let V := Matrix.vandermonde z
  let y := V.mulVec a
  have hy (i : Fin n) : y i = polynomialSample a (z i) := by
    simp only [y, V, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
      polynomialSample, mul_comm]
  have hc : V.adjugate.mulVec y = V.det • a := by
    change V.adjugate.mulVec (V.mulVec a) = _
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hj := congrArg (fun v : Fin n → ℂ => v j) hc
  have hB := one_le_phaseFrequencyScale z
  have hentry := norm_vandermonde_apply_le_pow hB (norm_le_phaseFrequencyScale z)
  calc
    ‖(Matrix.vandermonde z).det‖ * ‖a j‖ = ‖V.det * a j‖ := by rw [norm_mul]
    _ = ‖∑ i, V.adjugate j i * y i‖ := by
      rw [show V.det * a j = V.adjugate.mulVec y j by
        simpa only [Pi.smul_apply, smul_eq_mul] using hj.symm]
      rfl
    _ ≤ ∑ i, ‖V.adjugate j i * y i‖ := norm_sum_le _ _
    _ ≤ ∑ i, polynomialSamplingCap z * ‖y i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_adjugate_apply_le_factorial_mul_pow V (one_le_pow₀ hB) hentry j i)
        (norm_nonneg _)
    _ = _ := by simp only [← Finset.mul_sum, hy]

/-- Quadratic energy version of the full interpolation bound. -/
theorem polynomialSample_energy_bound {n : ℕ} (z a : Fin n → ℂ) :
    ‖(Matrix.vandermonde z).det‖ ^ 2 * (∑ j, ‖a j‖ ^ 2) ≤
      (n : ℝ) ^ 2 * polynomialSamplingCap z ^ 2 *
        ∑ i, ‖polynomialSample a (z i)‖ ^ 2 := by
  classical
  have hC : 0 ≤ polynomialSamplingCap z := by
    unfold polynomialSamplingCap
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
      (pow_nonneg (zero_le_one.trans (one_le_phaseFrequencyScale z)) _) _)
  have hsum : (∑ i, ‖polynomialSample a (z i)‖) ^ 2 ≤
      (n : ℝ) * ∑ i, ‖polynomialSample a (z i)‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun i => ‖polynomialSample a (z i)‖)
  have hcoord (j : Fin n) :
      ‖(Matrix.vandermonde z).det‖ ^ 2 * ‖a j‖ ^ 2 ≤
        polynomialSamplingCap z ^ 2 * ((n : ℝ) * ∑ i, ‖polynomialSample a (z i)‖ ^ 2) := by
    have h := (sq_le_sq₀ (by positivity) (by positivity)).2
      (polynomialSample_coefficient_bound z a j)
    rw [mul_pow, mul_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
  calc
    _ = ∑ j, ‖(Matrix.vandermonde z).det‖ ^ 2 * ‖a j‖ ^ 2 := Finset.mul_sum ..
    _ ≤ ∑ _j : Fin n, polynomialSamplingCap z ^ 2 *
        ((n : ℝ) * ∑ i, ‖polynomialSample a (z i)‖ ^ 2) :=
      Finset.sum_le_sum (fun j _ => hcoord j)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end
end GaloisForLFunctions.HTGeometry

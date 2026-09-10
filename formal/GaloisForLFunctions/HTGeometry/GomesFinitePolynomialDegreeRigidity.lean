import GaloisForLFunctions.HTGeometry.GomesGroundTensorEigenstateBoundary

/-!
# Degree rigidity under finite polynomial tensor composition

In the scalar Gomes experiment, tensor multiplication adds polynomial log-densities.
Finiteness forces negative leading coefficients, so the dominant degree cannot cancel.
The exceptional quadratic eigenstate class therefore survives composition exactly when
both factors already belong to it.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Finite tensor composition retains exactly the larger polynomial degree. -/
theorem gomesFinitePolynomialProfile_add_natDegree (P Q : GomesFinitePolynomialProfile) :
    (P.val + Q.val).natDegree = max P.val.natDegree Q.val.natDegree := by
  rcases lt_trichotomy P.val.natDegree Q.val.natDegree with h | h | h
  · rw [natDegree_add_eq_right_of_natDegree_lt h, max_eq_right h.le]
  · apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_add_le _ _)
    have hP := ((gomesFinitePolynomialProfiles_mem_iff P.val).mp P.property).2.2
    have hQ := ((gomesFinitePolynomialProfiles_mem_iff Q.val).mp Q.property).2.2
    rw [h, max_self, coeff_add, ← h, coeff_natDegree, h, coeff_natDegree]
    exact ne_of_lt (add_neg hP hQ)
  · rw [natDegree_add_eq_left_of_natDegree_lt h, max_eq_left h.le]

/-- Every degree threshold is respected factor by factor by finite tensor composition. -/
theorem gomesFinitePolynomialProfile_add_degree_le_iff
    (P Q : GomesFinitePolynomialProfile) (n : ℕ) :
    (P.val + Q.val).natDegree ≤ n ↔ P.val.natDegree ≤ n ∧ Q.val.natDegree ≤ n := by
  rw [gomesFinitePolynomialProfile_add_natDegree, max_le_iff]

/-- Vanishing third derivative is exactly the quadratic degree bound. -/
theorem gomesPolynomial_third_derivative_zero_iff_degree (H : ℝ[X]) :
    H.derivative.derivative.derivative = 0 ↔ H.natDegree ≤ 2 := by
  rw [derivative_eq_zero, natDegree_derivative, natDegree_derivative, Nat.sub_sub]
  exact Nat.sub_eq_zero_iff_le

/-- Two finite profiles combine to a quadratic exactly when both are quadratic. -/
theorem gomesFinitePolynomialProfile_add_quadratic_iff (P Q : GomesFinitePolynomialProfile) :
    (P.val + Q.val).derivative.derivative.derivative = 0 ↔
      P.val.derivative.derivative.derivative = 0 ∧
        Q.val.derivative.derivative.derivative = 0 := by
  simp only [gomesPolynomial_third_derivative_zero_iff_degree,
    gomesFinitePolynomialProfile_add_degree_le_iff]

/-- Exceptional positive tensor energy requires both factors to be quadratic. -/
theorem gomesPolynomialGroundTensor_positive_eigen_factors_iff
    (P Q : GomesFinitePolynomialProfile) :
    (∃ (K : ℝ[X]) (e : ℝ), 0 < e ∧
      dilatonHamiltonianCLM K (mulS (gomesPolynomialGroundState P)
        (gomesPolynomialGroundState Q)) =
          (e : ℂ) • mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q)) ↔
      P.val.derivative.derivative.derivative = 0 ∧
        Q.val.derivative.derivative.derivative = 0 := by
  rw [gomesPolynomialGroundTensor_positive_eigen_iff,
    gomesFinitePolynomialProfile_add_quadratic_iff]

/-- One higher-degree factor rules out every positive-energy target for the product state. -/
theorem gomesPolynomialGroundTensor_positive_eigen_obstruction
    (P Q : GomesFinitePolynomialProfile) :
    (¬ ∃ (K : ℝ[X]) (e : ℝ), 0 < e ∧
      dilatonHamiltonianCLM K (mulS (gomesPolynomialGroundState P)
        (gomesPolynomialGroundState Q)) =
          (e : ℂ) • mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q)) ↔
      P.val.derivative.derivative.derivative ≠ 0 ∨
        Q.val.derivative.derivative.derivative ≠ 0 := by
  rw [gomesPolynomialGroundTensor_positive_eigen_factors_iff, not_and_or]

end GaloisForLFunctions.HTGeometry

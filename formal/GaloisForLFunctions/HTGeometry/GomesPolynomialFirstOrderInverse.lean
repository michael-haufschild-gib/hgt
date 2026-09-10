import GaloisForLFunctions.HTGeometry.GomesPolynomialFirstOrderSolvability
import GaloisForLFunctions.HTGeometry.PolynomialSmoothApproximation

/-!
# Complete polynomial first-order inversion

The polynomial connection operator has an exact three-way classification: differentiation
is surjective with a constant kernel, a nonzero constant coefficient gives an isomorphism,
and every nonconstant coefficient gives an injective operator with a proper range.
The missing existence proof descends in the degree of the forcing polynomial.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Every constant coefficient admits a polynomial solution for every polynomial forcing. -/
theorem gomesPolynomialFirstOrderOperator_constant_surjective (a : ℝ) :
    Function.Surjective (gomesPolynomialFirstOrderOperator (C a)) := by
  intro Q
  by_cases ha : a = 0
  · exact ⟨realAntiderivative Q, by simp [ha, gomesPolynomialFirstOrderOperator,
      derivative_realAntiderivative]⟩
  · have hall : ∀ n : ℕ, ∀ Q : ℝ[X], Q.natDegree = n →
        ∃ B, gomesPolynomialFirstOrderOperator (C a) B = Q := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro Q hQ
        by_cases hz : Q.natDegree = 0
        · rw [eq_C_of_natDegree_eq_zero hz]
          exact (gomesPolynomialFirstOrderOperator_constant_range_iff (C a) (Q.coeff 0)).mpr
            (Or.inr derivative_C)
        · obtain ⟨B, hB⟩ := ih Q.derivative.natDegree
            (hQ ▸ natDegree_derivative_lt hz) Q.derivative rfl
          refine ⟨C a⁻¹ * (B - Q), ?_⟩
          unfold gomesPolynomialFirstOrderOperator at hB ⊢
          simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub]
          have hunit : C a * C a⁻¹ = (1 : ℝ[X]) := by
            rw [← C_mul, mul_inv_cancel₀ ha, map_one]
          linear_combination C a⁻¹ * hB + Q * hunit
    exact hall Q.natDegree Q rfl

/-- Full surjectivity occurs exactly for constant polynomial coefficients. -/
theorem gomesPolynomialFirstOrderOperator_surjective_iff (A : ℝ[X]) :
    Function.Surjective (gomesPolynomialFirstOrderOperator A) ↔ A.derivative = 0 := by
  constructor
  · intro hs
    have h := (gomesPolynomialFirstOrderOperator_constant_range_iff A 1).mp (hs (C 1))
    exact h.resolve_left one_ne_zero
  · intro h
    rw [eq_C_of_derivative_eq_zero h]
    exact gomesPolynomialFirstOrderOperator_constant_surjective _

/-- Polynomial connection inversion is bijective exactly for nonzero constant coefficients. -/
theorem gomesPolynomialFirstOrderOperator_bijective_iff (A : ℝ[X]) :
    Function.Bijective (gomesPolynomialFirstOrderOperator A) ↔ A ≠ 0 ∧ A.derivative = 0 := by
  rw [Function.Bijective, gomesPolynomialFirstOrderOperator_injective_iff,
    gomesPolynomialFirstOrderOperator_surjective_iff]

/-- Solvability of every forcing with uniqueness is exactly the nonzero constant case. -/
theorem gomesPolynomialFirstOrderOperator_all_unique_iff (A : ℝ[X]) :
    (∀ Q : ℝ[X], ∃! B : ℝ[X], gomesPolynomialFirstOrderOperator A B = Q) ↔
      A ≠ 0 ∧ A.derivative = 0 := by
  constructor
  · intro h
    have hs : Function.Surjective (gomesPolynomialFirstOrderOperator A) := fun Q => (h Q).exists
    have hi : Function.Injective (gomesPolynomialFirstOrderOperator A) := by
      intro B D hBD
      obtain ⟨E, _, hE⟩ := h (gomesPolynomialFirstOrderOperator A D)
      exact (hE B hBD).trans (hE D rfl).symm
    exact (gomesPolynomialFirstOrderOperator_bijective_iff A).mp ⟨hi, hs⟩
  · intro h Q
    have hb := (gomesPolynomialFirstOrderOperator_bijective_iff A).mpr h
    obtain ⟨B, hB⟩ := hb.2 Q
    exact ⟨B, hB, fun D hD => hb.1 (hD.trans hB.symm)⟩

/-- The first-order polynomial connection as a real linear map. -/
def gomesPolynomialFirstOrderLinearMap (A : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := gomesPolynomialFirstOrderOperator A
  map_add' := by intro B D; simp [gomesPolynomialFirstOrderOperator, mul_add]; ring
  map_smul' := by
    intro r B
    simp [gomesPolynomialFirstOrderOperator, smul_sub]

/-- A nonzero constant connection gives an actual linear equivalence on all polynomials. -/
def gomesPolynomialFirstOrderEquiv (a : ℝˣ) : ℝ[X] ≃ₗ[ℝ] ℝ[X] :=
  LinearEquiv.ofBijective (gomesPolynomialFirstOrderLinearMap (C (a : ℝ)))
    ((gomesPolynomialFirstOrderOperator_bijective_iff _).mpr
      ⟨by simpa only [ne_eq, C_eq_zero] using a.ne_zero, derivative_C⟩)

/-- The inverse solves every polynomial forcing exactly. -/
theorem gomesPolynomialFirstOrderEquiv_inverse_solves (a : ℝˣ) (Q : ℝ[X]) :
    gomesPolynomialFirstOrderOperator (C (a : ℝ))
      ((gomesPolynomialFirstOrderEquiv a).symm Q) = Q :=
  (gomesPolynomialFirstOrderEquiv a).apply_symm_apply Q

/-- Inversion commutes with differentiating the forcing. -/
theorem gomesPolynomialFirstOrderEquiv_inverse_derivative (a : ℝˣ) (Q : ℝ[X]) :
    ((gomesPolynomialFirstOrderEquiv a).symm Q).derivative =
      (gomesPolynomialFirstOrderEquiv a).symm Q.derivative := by
  apply (gomesPolynomialFirstOrderOperator_injective_iff (C (a : ℝ))).mpr
    (by simpa only [ne_eq, C_eq_zero] using a.ne_zero)
  rw [gomesPolynomialFirstOrderEquiv_inverse_solves]
  have h := congrArg Polynomial.derivative (gomesPolynomialFirstOrderEquiv_inverse_solves a Q)
  simpa only [gomesPolynomialFirstOrderOperator, derivative_sub, derivative_mul,
    derivative_C, zero_mul, zero_add] using h

/-- Inversion obeys the degree-descending reconstruction equation. -/
theorem gomesPolynomialFirstOrderEquiv_inverse_recursion (a : ℝˣ) (Q : ℝ[X]) :
    (gomesPolynomialFirstOrderEquiv a).symm Q =
      C ((a : ℝ)⁻¹) * ((gomesPolynomialFirstOrderEquiv a).symm Q.derivative - Q) := by
  have h := gomesPolynomialFirstOrderEquiv_inverse_solves a Q
  unfold gomesPolynomialFirstOrderOperator at h
  rw [gomesPolynomialFirstOrderEquiv_inverse_derivative] at h
  have hunit : C (a : ℝ) * C ((a : ℝ)⁻¹) = (1 : ℝ[X]) := by
    rw [← C_mul, mul_inv_cancel₀ a.ne_zero, map_one]
  linear_combination -C ((a : ℝ)⁻¹) * h -
    (gomesPolynomialFirstOrderEquiv a).symm Q * hunit

end GaloisForLFunctions.HTGeometry

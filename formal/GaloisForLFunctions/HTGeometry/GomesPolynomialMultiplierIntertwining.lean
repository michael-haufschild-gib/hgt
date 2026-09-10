import GaloisForLFunctions.HTGeometry.GomesPolynomialMultiplicationCommutant

/-!
# Exact rigidity of multiplication-compatible connection maps

After retaining coordinate multiplication, an intertwiner between polynomial
connections is either zero, or a constant scalar map between identical coefficients.
The differential equation for its multiplier supplies the entire obstruction.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Multiplier intertwining is exactly the logarithmic-derivative equation for that multiplier. -/
theorem gomesPolynomialMultiplier_intertwining_equation (A B P : ℝ[X]) :
    (gomesPolynomialMultiplicationMap P).comp (gomesPolynomialFirstOrderLinearMap A) =
        (gomesPolynomialFirstOrderLinearMap B).comp (gomesPolynomialMultiplicationMap P) ↔
      P.derivative = (B - A) * P := by
  constructor
  · intro h
    have he := congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f 1) h
    change P * gomesPolynomialFirstOrderOperator A 1 =
      gomesPolynomialFirstOrderOperator B (P * 1) at he
    simp only [gomesPolynomialFirstOrderOperator, derivative_one, zero_sub, mul_one] at he
    linear_combination -he
  · intro h
    apply LinearMap.ext
    intro Q
    change P * gomesPolynomialFirstOrderOperator A Q =
      gomesPolynomialFirstOrderOperator B (P * Q)
    simp only [gomesPolynomialFirstOrderOperator, derivative_mul, h]
    ring

/-- A nonzero polynomial multiplier can intertwine only identical connections, and must be constant. -/
theorem gomesPolynomialMultiplier_intertwines_iff (A B P : ℝ[X]) :
    (gomesPolynomialMultiplicationMap P).comp (gomesPolynomialFirstOrderLinearMap A) =
        (gomesPolynomialFirstOrderLinearMap B).comp (gomesPolynomialMultiplicationMap P) ↔
      P = 0 ∨ (A = B ∧ P.derivative = 0) := by
  rw [gomesPolynomialMultiplier_intertwining_equation]
  constructor
  · intro h
    by_cases hp : P = 0
    · exact Or.inl hp
    · have hab : A = B := by
        by_contra hn
        have hi := (gomesPolynomialFirstOrderOperator_injective_iff (B - A)).mpr
          (sub_ne_zero.mpr (Ne.symm hn))
        apply hp
        apply hi
        simp only [gomesPolynomialFirstOrderOperator, h, sub_self, derivative_zero,
          mul_zero]
      exact Or.inr ⟨hab, by simpa only [hab, sub_self, zero_mul] using h⟩
  · rintro (rfl | ⟨rfl, hp⟩)
    · simp only [derivative_zero, mul_zero]
    · simp only [hp, sub_self, zero_mul]

/-- The multiplier equation has exactly the zero map and scalar identity solutions. -/
theorem gomesPolynomialMultiplier_intertwines_constant_iff (A B P : ℝ[X]) :
    (gomesPolynomialMultiplicationMap P).comp (gomesPolynomialFirstOrderLinearMap A) =
        (gomesPolynomialFirstOrderLinearMap B).comp (gomesPolynomialMultiplicationMap P) ↔
      P = 0 ∨ (A = B ∧ ∃ c : ℝ, P = C c) := by
  rw [gomesPolynomialMultiplier_intertwines_iff]
  constructor
  · rintro (hp | ⟨hab, hp⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨hab, P.coeff 0, eq_C_of_derivative_eq_zero hp⟩
  · rintro (hp | ⟨hab, c, rfl⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨hab, derivative_C⟩

/-- Complete classification of every linear map preserving both the coordinate action and connection. -/
theorem gomesPolynomialConnection_coordinate_compatible_maps_iff
    (A B : ℝ[X]) (E : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    (E.comp (gomesPolynomialMultiplicationMap X) =
        (gomesPolynomialMultiplicationMap X).comp E ∧
      E.comp (gomesPolynomialFirstOrderLinearMap A) =
        (gomesPolynomialFirstOrderLinearMap B).comp E) ↔
      E = 0 ∨ (A = B ∧ ∃ c : ℝ, E = c • (LinearMap.id : ℝ[X] →ₗ[ℝ] ℝ[X])) := by
  constructor
  · rintro ⟨hx, ht⟩
    have he := (gomesPolynomialMultiplication_X_commutant_iff E).mp hx
    rw [he] at ht
    rcases (gomesPolynomialMultiplier_intertwines_constant_iff A B (E 1)).mp ht with
      hz | ⟨hab, c, hc⟩
    · left
      rw [he, hz]
      apply LinearMap.ext
      intro Q
      simp only [gomesPolynomialMultiplicationMap, LinearMap.mul_apply', zero_mul,
        LinearMap.zero_apply]
    · exact Or.inr ⟨hab, c, by rw [he, hc, gomesPolynomialMultiplicationMap_constant]⟩
  · rintro (rfl | ⟨rfl, c, rfl⟩)
    · constructor <;> apply LinearMap.ext <;> intro Q <;> simp
    · constructor <;> apply LinearMap.ext <;> intro Q <;> simp

/-- For a coordinate-compatible map, nontrivial connection intertwining already forces coefficient equality. -/
theorem gomesPolynomialConnection_nonzero_coordinate_map_coefficient
    (A B : ℝ[X])
    (E : {E : GomesPolynomialXCompatibleMap //
      E.val ≠ 0 ∧ E.val.comp (gomesPolynomialFirstOrderLinearMap A) =
        (gomesPolynomialFirstOrderLinearMap B).comp E.val}) : A = B := by
  have h := (gomesPolynomialConnection_coordinate_compatible_maps_iff A B E.val.val).mp
    ⟨E.val.property, E.property.2⟩
  rcases h with hz | ⟨hab, _⟩
  · exact False.elim (E.property.1 hz)
  · exact hab

end GaloisForLFunctions.HTGeometry

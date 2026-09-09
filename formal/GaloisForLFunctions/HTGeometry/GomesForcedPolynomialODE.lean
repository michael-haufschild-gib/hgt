import GaloisForLFunctions.HTGeometry.GomesPolynomialHamiltonianFibers

/-!
# Polynomial first-order equations with constant forcing

The constant-energy extension of the Gomes scalar reconstruction experiment reduces
to a forced polynomial logarithmic-derivative equation. Degree and divisibility force
its exact dichotomy: a constant solution or an affine solution with zero coefficient.
This infrastructure will classify constant differences of polynomial Riccati images.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Constant forcing permits only a constant solution or a vanishing multiplication coefficient. -/
theorem gomesPolynomialDerivative_forced_iff (A B : ℝ[X]) (c : ℝ) :
    B.derivative = A * B + C c ↔
      (B.derivative = 0 ∧ A * B = -C c) ∨ (A = 0 ∧ B.derivative = C c) := by
  constructor
  · intro h
    by_cases hdeg : B.degree ≤ 0
    · have hb := eq_C_of_degree_le_zero hdeg
      have hd : B.derivative = 0 := by rw [hb, derivative_C]
      exact Or.inl ⟨hd, by linear_combination hd - h⟩
    · have hpos : 0 < B.degree := lt_of_not_ge hdeg
      have hb : B ≠ 0 := by
        rintro rfl
        simp only [degree_zero, not_lt_bot] at hpos
      have hdvd : B ∣ B.derivative - C c := by
        refine ⟨A, ?_⟩
        linear_combination h
      have hsmall : (B.derivative - C c).degree < B.degree :=
        (degree_sub_le _ _).trans_lt
          (max_lt (degree_derivative_lt hb) (degree_C_le.trans_lt hpos))
      have hd : B.derivative = C c :=
        sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hdvd hsmall)
      have hp : A * B = 0 := by linear_combination hd - h
      exact Or.inr ⟨(mul_eq_zero.mp hp).resolve_right hb, hd⟩
  · rintro (⟨hd, hp⟩ | ⟨rfl, hd⟩)
    · rw [hd, hp, neg_add_cancel]
    · rw [zero_mul, zero_add]
      exact hd

/-- Every polynomial solution belongs to an explicit constant or affine family. -/
theorem gomesPolynomialDerivative_forced_profiles (A B : ℝ[X]) (c : ℝ) :
    B.derivative = A * B + C c ↔
      (∃ b : ℝ, B = C b ∧ A * C b = -C c) ∨
        (A = 0 ∧ ∃ b : ℝ, B = C c * X + C b) := by
  rw [gomesPolynomialDerivative_forced_iff, gomesDilatonDerivative_constant_iff]
  constructor
  · rintro (⟨hd, hp⟩ | ha)
    · let b := B.coeff 0
      have hb : B = C b := eq_C_of_derivative_eq_zero hd
      exact Or.inl ⟨b, hb, by rwa [hb] at hp⟩
    · exact Or.inr ha
  · rintro (⟨b, rfl, hp⟩ | ha)
    · exact Or.inl ⟨derivative_C, hp⟩
    · exact Or.inr ha

/-- Nonconstant solutions have a uniquely forced slope and zero multiplication coefficient. -/
theorem gomesPolynomialDerivative_forced_nonconstant_iff
    (B : {B : ℝ[X] // B.derivative ≠ 0}) (A : ℝ[X]) (c : ℝ) :
    B.val.derivative = A * B.val + C c ↔
      A = 0 ∧ ∃ b : ℝ, B.val = C c * X + C b := by
  rw [gomesPolynomialDerivative_forced_iff]
  constructor
  · rintro (⟨hz, _⟩ | ⟨ha, hd⟩)
    · exact False.elim (B.property hz)
    · exact ⟨ha, (gomesDilatonDerivative_constant_iff B.val c).mp hd⟩
  · rintro ⟨ha, hb⟩
    exact Or.inr ⟨ha, (gomesDilatonDerivative_constant_iff B.val c).mpr hb⟩

/-- The inhomogeneous equation forces its constant and product parts separately whenever A is nonzero. -/
theorem gomesPolynomialDerivative_forced_nonzero_coefficient_iff
    (A : {A : ℝ[X] // A ≠ 0}) (B : ℝ[X]) (c : ℝ) :
    B.derivative = A.val * B + C c ↔
      ∃ b : ℝ, B = C b ∧ A.val * C b = -C c := by
  rw [gomesPolynomialDerivative_forced_profiles]
  constructor
  · rintro (h | ⟨ha, _⟩)
    · exact h
    · exact False.elim (A.property ha)
  · exact Or.inl

end GaloisForLFunctions.HTGeometry

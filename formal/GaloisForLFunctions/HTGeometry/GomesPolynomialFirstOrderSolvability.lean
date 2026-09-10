import GaloisForLFunctions.HTGeometry.GomesForcedPolynomialODE

/-!
# Solvability and faithful reconstruction for polynomial first-order operators

The forced ODE arising in the Gomes reconstruction experiment has a positive survivor:
its full constant-forcing solvability criterion and exact observational fibers. A nonzero
polynomial coefficient makes the first-order operator injective, whereas zero coefficient
loses exactly the additive constant. Nonzero constant forcing is possible only for a
constant coefficient, with every solution explicitly classified.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The actual polynomial differential operator with multiplication coefficient A. -/
def gomesPolynomialFirstOrderOperator (A B : ℝ[X]) : ℝ[X] := B.derivative - A * B

/-- Equality of first-order observations loses exactly a constant when the coefficient vanishes. -/
theorem gomesPolynomialFirstOrderOperator_fibers (A B D : ℝ[X]) :
    gomesPolynomialFirstOrderOperator A B = gomesPolynomialFirstOrderOperator A D ↔
      B = D ∨ (A = 0 ∧ ∃ c : ℝ, B = D + C c) := by
  constructor
  · intro h
    have hd : (B - D).derivative = A * (B - D) := by
      simp only [derivative_sub]
      unfold gomesPolynomialFirstOrderOperator at h
      linear_combination h
    rcases (gomesPolynomialDerivative_multiple_iff A (B - D)).mp hd with hz | ⟨ha, hd⟩
    · exact Or.inl (sub_eq_zero.mp hz)
    · refine Or.inr ⟨ha, (gomesDilatonDerivative_eq_iff B D).mp ?_⟩
      simpa only [derivative_sub, sub_eq_zero] using hd
  · rintro (rfl | ⟨rfl, c, rfl⟩)
    · rfl
    · simp [gomesPolynomialFirstOrderOperator]

/-- Every nonzero polynomial coefficient makes its full first-order observation injective. -/
theorem gomesPolynomialFirstOrderOperator_injective_iff (A : ℝ[X]) :
    Function.Injective (gomesPolynomialFirstOrderOperator A) ↔ A ≠ 0 := by
  constructor
  · intro hi hz
    have he : gomesPolynomialFirstOrderOperator A 0 = gomesPolynomialFirstOrderOperator A 1 := by
      rw [hz]
      simp [gomesPolynomialFirstOrderOperator]
    exact zero_ne_one (hi he)
  · intro ha B D h
    exact ((gomesPolynomialFirstOrderOperator_fibers A B D).mp h).resolve_right
      (fun h => ha h.1)

/-- Constant forcing has a polynomial solution exactly when it is zero or the coefficient is constant. -/
theorem gomesPolynomialDerivative_forced_solvable_iff (A : ℝ[X]) (c : ℝ) :
    (∃ B : ℝ[X], B.derivative = A * B + C c) ↔ c = 0 ∨ A.derivative = 0 := by
  constructor
  · rintro ⟨B, h⟩
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rcases (gomesPolynomialDerivative_forced_profiles A B c).mp h with ⟨b, _, hp⟩ | ⟨ha, _⟩
      · have hb : (C b : ℝ[X]) ≠ 0 := by
          intro hz
          rw [hz, mul_zero] at hp
          apply hc
          apply C_injective
          simpa only [map_zero] using (neg_eq_zero.mp hp.symm)
        have hd := congrArg Polynomial.derivative hp
        simp only [derivative_mul, derivative_C, derivative_neg, mul_zero, add_zero, neg_zero] at hd
        exact (mul_eq_zero.mp hd).resolve_right hb
      · rw [ha, derivative_zero]
  · rintro (rfl | ha)
    · exact ⟨0, by simp⟩
    · let a := A.coeff 0
      have hA : A = C a := eq_C_of_derivative_eq_zero ha
      by_cases hz : a = 0
      · refine ⟨C c * X, ?_⟩
        rw [hA, hz]
        simp
      · refine ⟨C (-c / a), ?_⟩
        apply Polynomial.funext
        intro x
        rw [hA]
        simp only [derivative_C, eval_zero, eval_add, eval_mul, eval_C]
        field_simp [hz]
        ring

/-- The constant part of the operator range is either all constants or only zero. -/
theorem gomesPolynomialFirstOrderOperator_constant_range_iff (A : ℝ[X]) (c : ℝ) :
    (∃ B : ℝ[X], gomesPolynomialFirstOrderOperator A B = C c) ↔ c = 0 ∨ A.derivative = 0 := by
  rw [← gomesPolynomialDerivative_forced_solvable_iff]
  constructor <;> rintro ⟨B, h⟩ <;> refine ⟨B, ?_⟩
  · unfold gomesPolynomialFirstOrderOperator at h
    linear_combination h
  · unfold gomesPolynomialFirstOrderOperator
    linear_combination h

/-- Nonconstant coefficients admit no nonzero constant output, despite having injective observations. -/
theorem gomesPolynomialFirstOrderOperator_nonconstant_constant_iff
    (A : {A : ℝ[X] // A.derivative ≠ 0}) (c : ℝ) :
    (∃ B : ℝ[X], gomesPolynomialFirstOrderOperator A.val B = C c) ↔ c = 0 := by
  rw [gomesPolynomialFirstOrderOperator_constant_range_iff]
  exact or_iff_left A.property

/-- A specified constant forcing has a unique polynomial solution exactly when the coefficient is nonzero and solvability holds. -/
theorem gomesPolynomialFirstOrderOperator_unique_constant_iff (A : ℝ[X]) (c : ℝ) :
    (∃! B : ℝ[X], gomesPolynomialFirstOrderOperator A B = C c) ↔
      A ≠ 0 ∧ (c = 0 ∨ A.derivative = 0) := by
  constructor
  · rintro ⟨B, hB, huniq⟩
    refine ⟨?_, (gomesPolynomialFirstOrderOperator_constant_range_iff A c).mp ⟨B, hB⟩⟩
    intro hz
    have hplus : gomesPolynomialFirstOrderOperator A (B + C 1) = C c := by
      have he := (gomesPolynomialFirstOrderOperator_fibers A (B + C 1) B).mpr
        (Or.inr ⟨hz, 1, rfl⟩)
      exact he.trans hB
    have he := huniq (B + C 1) hplus
    have hx := congrArg (Polynomial.eval 0) he
    simp only [eval_add, eval_C] at hx
    linarith
  · rintro ⟨ha, hc⟩
    obtain ⟨B, hB⟩ := (gomesPolynomialFirstOrderOperator_constant_range_iff A c).mpr hc
    refine ⟨B, hB, ?_⟩
    intro D hD
    exact (gomesPolynomialFirstOrderOperator_injective_iff A).mpr ha (hD.trans hB.symm)

end GaloisForLFunctions.HTGeometry

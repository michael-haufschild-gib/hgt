import GaloisForLFunctions.HTGeometry.GomesPolynomialRiccatiEnergyShifts

/-!
# Every constant energy difference between polynomial dilaton potentials

The scalar reconstruction question prompted by arXiv:2607.24901v1 section 4 has
an exact energy-reference classification. Besides the constant log-amplitude family,
only affine profiles and opposite quadratic profiles can produce constant differences.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A constant half-drift records the exact slope of its profile. -/
theorem gomesDilatonConnectionPolynomial_constant_iff (H : ℝ[X]) (a : ℝ) :
    gomesDilatonConnectionPolynomial H = C a ↔ H.derivative = C (2 * a) := by
  constructor <;> intro h <;> apply Polynomial.funext <;> intro x
  · have hx := congrArg (Polynomial.eval x) h
    simp only [gomesDilatonConnectionPolynomial, eval_mul, eval_C] at hx ⊢
    linarith
  · have hx := congrArg (Polynomial.eval x) h
    simp only [gomesDilatonConnectionPolynomial, eval_mul, eval_C] at hx ⊢
    linarith

/-- A constant half-drift derivative records the exact profile curvature. -/
theorem gomesDilatonConnectionPolynomial_derivative_constant_iff (H : ℝ[X]) (a : ℝ) :
    (gomesDilatonConnectionPolynomial H).derivative = C a ↔
      H.derivative.derivative = C (2 * a) := by
  constructor <;> intro h <;> apply Polynomial.funext <;> intro x
  · have hx := congrArg (Polynomial.eval x) h
    simp only [gomesDilatonConnectionPolynomial, derivative_C_mul, eval_mul, eval_C] at hx ⊢
    linarith
  · have hx := congrArg (Polynomial.eval x) h
    simp only [gomesDilatonConnectionPolynomial, derivative_C_mul, eval_mul, eval_C] at hx ⊢
    linarith

/-- A scalar energy difference is exactly a constant difference of the potential polynomials. -/
theorem gomesDilatonPotential_shifted_polynomial_iff (H K : ℝ[X]) (k : ℝ) :
    (∀ x : ℝ, dilatonPotential H x = dilatonPotential K x + k) ↔
      gomesDilatonPotentialPolynomial H = gomesDilatonPotentialPolynomial K + C k := by
  constructor
  · intro h
    apply Polynomial.funext
    intro x
    rw [eval_add, eval_C, gomesDilatonPotentialPolynomial_eval,
      gomesDilatonPotentialPolynomial_eval, h]
  · intro h x
    have hx := congrArg (Polynomial.eval x) h
    simpa only [eval_add, eval_C, gomesDilatonPotentialPolynomial_eval] using hx

/-- Complete derivative-level classification of all polynomial potential energy shifts. -/
theorem gomesDilatonPotential_shifted_derivatives_iff (H K : ℝ[X]) (k : ℝ) :
    (∀ x : ℝ, dilatonPotential H x = dilatonPotential K x + k) ↔
      (H.derivative = K.derivative ∧ k = 0) ∨
        (∃ a b : ℝ, H.derivative = C (2 * a) ∧ K.derivative = C (2 * b) ∧
          a ^ (2 : ℕ) = b ^ (2 : ℕ) + k) ∨
            (H.derivative = -K.derivative ∧ H.derivative.derivative = C k) := by
  rw [gomesDilatonPotential_shifted_polynomial_iff]
  change gomesPolynomialRiccati (gomesDilatonConnectionPolynomial H) =
    gomesPolynomialRiccati (gomesDilatonConnectionPolynomial K) + C k ↔ _
  rw [gomesPolynomialRiccati_shifted_iff, gomesDilatonConnectionPolynomial_eq_iff]
  simp only [gomesDilatonConnectionPolynomial_constant_iff,
    ← gomesDilatonConnectionPolynomial_neg, gomesDilatonConnectionPolynomial_eq_iff,
    derivative_neg, gomesDilatonConnectionPolynomial_derivative_constant_iff,
    show (2 : ℝ) * (k / 2) = k by ring]

/-- Complete profile-level trichotomy, including the exact opposite quadratic coefficient. -/
theorem gomesDilatonPotential_shifted_profiles_iff (H K : ℝ[X]) (k : ℝ) :
    (∀ x : ℝ, dilatonPotential H x = dilatonPotential K x + k) ↔
      ((∃ c : ℝ, H = K + C c) ∧ k = 0) ∨
        (∃ a b c d : ℝ, H = C (2 * a) * X + C b ∧
          K = C (2 * c) * X + C d ∧ a ^ (2 : ℕ) = c ^ (2 : ℕ) + k) ∨
            ∃ a b c : ℝ, H = C (k / 2) * X ^ (2 : ℕ) + C a * X + C b ∧ K = -H + C c := by
  rw [gomesDilatonPotential_shifted_derivatives_iff]
  constructor
  · rintro (⟨he, hk⟩ | ⟨a, c, ha, hc, hk⟩ | ⟨hu, hd⟩)
    · exact Or.inl ⟨(gomesDilatonDerivative_eq_iff H K).mp he, hk⟩
    · obtain ⟨b, hb⟩ := (gomesDilatonDerivative_constant_iff H (2 * a)).mp ha
      obtain ⟨d, hd⟩ := (gomesDilatonDerivative_constant_iff K (2 * c)).mp hc
      exact Or.inr (Or.inl ⟨a, b, c, d, hb, hd, hk⟩)
    · obtain ⟨a, b, hab⟩ := (gomesDilaton_secondDerivative_constant_iff H k).mp hd
      have hkd : K.derivative = (-H).derivative := by
        rw [derivative_neg]
        exact ((neg_eq_iff_eq_neg).mpr hu).symm
      obtain ⟨c, hc⟩ := (gomesDilatonDerivative_eq_iff K (-H)).mp hkd
      exact Or.inr (Or.inr ⟨a, b, c, hab, hc⟩)
  · rintro (⟨he, hk⟩ | ⟨a, b, c, d, hb, hd, hk⟩ | ⟨a, b, c, hab, hc⟩)
    · exact Or.inl ⟨(gomesDilatonDerivative_eq_iff H K).mpr he, hk⟩
    · exact Or.inr (Or.inl ⟨a, c,
        (gomesDilatonDerivative_constant_iff H (2 * a)).mpr ⟨b, hb⟩,
        (gomesDilatonDerivative_constant_iff K (2 * c)).mpr ⟨d, hd⟩, hk⟩)
    · refine Or.inr (Or.inr ⟨?_, (gomesDilaton_secondDerivative_constant_iff H k).mpr ⟨a, b, hab⟩⟩)
      rw [hc]
      simp

/-- Every energy reference difference occurs for an explicit pair of opposite quadratic profiles. -/
theorem gomesDilatonPotential_energy_shift_surjective (k : ℝ) :
    ∃ H K : ℝ[X], ∀ x : ℝ, dilatonPotential H x = dilatonPotential K x + k := by
  let H : ℝ[X] := C (k / 2) * X ^ (2 : ℕ)
  refine ⟨H, -H, (gomesDilatonPotential_shifted_profiles_iff H (-H) k).mpr ?_⟩
  exact Or.inr (Or.inr ⟨0, 0, 0, by simp [H], by simp⟩)

end GaloisForLFunctions.HTGeometry

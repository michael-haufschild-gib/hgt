import GaloisForLFunctions.HTGeometry.GomesPolynomialRiccatiFibers

/-!
# Polynomial reconstruction data for the dilaton Hamiltonian

This scalar reconstruction experiment associated with arXiv:2607.24901v1 section 4
identifies the exact polynomial Riccati data underlying the actual Schwartz operator.
The potential forgets only constant profile shifts and the opposite affine exception.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The half-logarithmic derivative entering the first-order dilaton factors. -/
def gomesDilatonConnectionPolynomial (H : ℝ[X]) : ℝ[X] := C (1 / 2 : ℝ) * H.derivative

/-- The polynomial whose evaluation is the scalar dilaton potential. -/
def gomesDilatonPotentialPolynomial (H : ℝ[X]) : ℝ[X] :=
  gomesPolynomialRiccati (gomesDilatonConnectionPolynomial H)

/-- Polynomial connection data retain exactly the derivative of the profile. -/
theorem gomesDilatonConnectionPolynomial_eq_iff (H K : ℝ[X]) :
    gomesDilatonConnectionPolynomial H = gomesDilatonConnectionPolynomial K ↔
      H.derivative = K.derivative := by
  constructor
  · intro h
    apply Polynomial.funext
    intro x
    have hx := congrArg (Polynomial.eval x) h
    simp only [gomesDilatonConnectionPolynomial, eval_mul, eval_C] at hx
    linarith
  · intro h
    simp only [gomesDilatonConnectionPolynomial, h]

/-- Dualizing the profile negates its polynomial connection. -/
theorem gomesDilatonConnectionPolynomial_neg (H : ℝ[X]) :
    gomesDilatonConnectionPolynomial (-H) = -gomesDilatonConnectionPolynomial H := by
  simp only [gomesDilatonConnectionPolynomial, derivative_neg, mul_neg]

/-- A constant polynomial connection is detected by the second profile derivative. -/
theorem gomesDilatonConnectionPolynomial_derivative_zero_iff (H : ℝ[X]) :
    (gomesDilatonConnectionPolynomial H).derivative = 0 ↔ H.derivative.derivative = 0 := by
  constructor
  · intro h
    apply Polynomial.funext
    intro x
    have hx := congrArg (Polynomial.eval x) h
    simp only [gomesDilatonConnectionPolynomial, derivative_C_mul, eval_mul, eval_C,
      eval_zero] at hx ⊢
    linarith
  · intro h
    simp only [gomesDilatonConnectionPolynomial, derivative_C_mul, h, mul_zero]

/-- Evaluation connects the algebraic Riccati map to the actual scalar potential. -/
theorem gomesDilatonPotentialPolynomial_eval (H : ℝ[X]) (x : ℝ) :
    (gomesDilatonPotentialPolynomial H).eval x = dilatonPotential H x := by
  simp only [gomesDilatonPotentialPolynomial, gomesPolynomialRiccati,
    gomesDilatonConnectionPolynomial, derivative_C_mul, eval_add, eval_mul, eval_C,
    eval_pow, dilatonPotential]
  ring

/-- Equality of scalar potentials is exactly equality of their polynomial representatives. -/
theorem gomesDilatonPotential_polynomial_eq_iff (H K : ℝ[X]) :
    dilatonPotential H = dilatonPotential K ↔
      gomesDilatonPotentialPolynomial H = gomesDilatonPotentialPolynomial K := by
  constructor
  · intro h
    apply Polynomial.funext
    intro x
    rw [gomesDilatonPotentialPolynomial_eval, gomesDilatonPotentialPolynomial_eval, h]
  · intro h
    funext x
    rw [← gomesDilatonPotentialPolynomial_eval, ← gomesDilatonPotentialPolynomial_eval, h]

/-- All polynomial scalar-potential coincidences have identical or opposite constant drifts. -/
theorem gomesDilatonPotential_derivative_fibers (H K : ℝ[X]) :
    dilatonPotential H = dilatonPotential K ↔
      H.derivative = K.derivative ∨
        (H.derivative = -K.derivative ∧ H.derivative.derivative = 0) := by
  rw [gomesDilatonPotential_polynomial_eq_iff]
  change gomesPolynomialRiccati (gomesDilatonConnectionPolynomial H) =
    gomesPolynomialRiccati (gomesDilatonConnectionPolynomial K) ↔ _
  rw [gomesPolynomialRiccati_eq_iff, gomesDilatonConnectionPolynomial_eq_iff,
    ← gomesDilatonConnectionPolynomial_neg, gomesDilatonConnectionPolynomial_eq_iff,
    derivative_neg, gomesDilatonConnectionPolynomial_derivative_zero_iff]

/-- The actual Schwartz Hamiltonian has precisely the same complete derivative classification. -/
theorem gomesDilatonHamiltonian_derivative_fibers (H K : ℝ[X]) :
    dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ↔
      H.derivative = K.derivative ∨
        (H.derivative = -K.derivative ∧ H.derivative.derivative = 0) := by
  rw [gomesDilatonHamiltonian_potential_eq_iff, gomesDilatonPotential_derivative_fibers]

/-- Equal Hamiltonians have separately equal curvature and squared drift, without compensation. -/
theorem gomesDilatonHamiltonian_parts_iff (H K : ℝ[X]) :
    dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ↔
      H.derivative.derivative = K.derivative.derivative ∧
        H.derivative ^ (2 : ℕ) = K.derivative ^ (2 : ℕ) := by
  constructor
  · intro h
    have hp := (gomesDilatonPotential_polynomial_eq_iff H K).mp
      ((gomesDilatonHamiltonian_potential_eq_iff H K).mp h)
    obtain ⟨hd, hs⟩ := (gomesPolynomialRiccati_eq_iff_parts _ _).mp hp
    constructor
    · apply Polynomial.funext
      intro x
      have hx := congrArg (Polynomial.eval x) hd
      simp only [gomesDilatonConnectionPolynomial, derivative_C_mul, eval_mul, eval_C] at hx
      linarith
    · apply Polynomial.funext
      intro x
      have hx := congrArg (Polynomial.eval x) hs
      simp only [gomesDilatonConnectionPolynomial, eval_pow, eval_mul, eval_C] at hx ⊢
      nlinarith
  · rintro ⟨hd, hs⟩
    apply (gomesDilatonHamiltonian_potential_eq_iff H K).mpr
    funext x
    have hx := congrArg (Polynomial.eval x) hs
    simp only [eval_pow] at hx
    simp only [dilatonPotential, hd, hx]

end GaloisForLFunctions.HTGeometry

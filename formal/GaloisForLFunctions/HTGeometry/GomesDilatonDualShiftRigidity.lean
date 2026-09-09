import GaloisForLFunctions.HTGeometry.GomesGaussianChargedConnection

/-!
# Rigidity of constant shifts under dualization of polynomial dilaton connections

Experimental application of dual tensor charges and the common induced connection:
duality always reverses the two first-order factors. The exact replacement for a constant
oscillator shift is multiplication by minus the second derivative of the log-weight.
Constant shifts occur precisely for quadratic-or-lower polynomial log-weights.
-/

noncomputable section
open Polynomial
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Dualization exchanges the two covariant first-order factors. -/
theorem gomesDilatonDual_supercharge (H : ℝ[X]) :
    dilatonSuperchargeCLM (-H) = -dilatonAdjointChargeCLM H := by
  ext ψ x
  change dilatonSuperchargeCLM (-H) ψ x = -(dilatonAdjointChargeCLM H ψ x)
  rw [dilatonSuperchargeCLM_apply, dilatonAdjointChargeCLM_apply]
  simp only [derivative_neg, eval_neg, Complex.ofReal_neg]
  ring

/-- The other first-order factor obeys the same dual exchange. -/
theorem gomesDilatonDual_adjointCharge (H : ℝ[X]) :
    dilatonAdjointChargeCLM (-H) = -dilatonSuperchargeCLM H := by
  ext ψ x
  change dilatonAdjointChargeCLM (-H) ψ x = -(dilatonSuperchargeCLM H ψ x)
  rw [dilatonAdjointChargeCLM_apply, dilatonSuperchargeCLM_apply]
  simp only [derivative_neg, eval_neg, Complex.ofReal_neg]
  ring

/-- The dual Hamiltonian reverses factor order on the actual Schwartz domain. -/
theorem gomesDilatonDual_factorization (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (-H) ψ = dilatonSuperchargeCLM H (dilatonAdjointChargeCLM H ψ) := by
  rw [dilatonHamiltonianCLM, ContinuousLinearMap.comp_apply,
    gomesDilatonDual_adjointCharge, gomesDilatonDual_supercharge]
  simp

/-- The exact dual potential correction is the negative second derivative of the log-weight. -/
theorem gomesDilatonDual_potential (H : ℝ[X]) (x : ℝ) :
    dilatonPotential (-H) x = dilatonPotential H x - H.derivative.derivative.eval x := by
  simp only [dilatonPotential, derivative_neg, eval_neg]
  ring

/-- The potential correction lifts to every actual Schwartz state pointwise. -/
theorem gomesDilatonDual_hamiltonian_apply (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonHamiltonianCLM (-H) ψ x = dilatonHamiltonianCLM H ψ x -
      ((H.derivative.derivative.eval x : ℝ) : ℂ) * ψ x := by
  rw [dilatonHamiltonianCLM_apply, dilatonHamiltonianCLM_apply, gomesDilatonDual_potential]
  push_cast
  ring

/-- The common connection determines the exact spatially varying commutator. -/
theorem gomesDilatonDual_commutator_apply (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (dilatonSuperchargeCLM H (dilatonAdjointChargeCLM H ψ) -
      dilatonAdjointChargeCLM H (dilatonSuperchargeCLM H ψ)) x =
      -((H.derivative.derivative.eval x : ℝ) : ℂ) * ψ x := by
  rw [← gomesDilatonDual_factorization]
  change dilatonHamiltonianCLM (-H) ψ x - dilatonHamiltonianCLM H ψ x = _
  rw [gomesDilatonDual_hamiltonian_apply]
  ring

/-- A spatially constant dual shift is exactly a constant second derivative. -/
theorem gomesDilatonDual_constant_shift_iff (H : ℝ[X]) (c : ℝ) :
    (∀ x : ℝ, dilatonPotential (-H) x = dilatonPotential H x + c) ↔
      H.derivative.derivative = C (-c) := by
  constructor
  · intro h
    apply Polynomial.funext
    intro x
    have hx := h x
    rw [gomesDilatonDual_potential] at hx
    simp only [eval_C]
    linarith
  · intro h x
    rw [gomesDilatonDual_potential, h, eval_C]
    ring

/-- Constant second derivative characterizes quadratic-or-lower polynomial log-weights exactly. -/
theorem gomesDilaton_secondDerivative_constant_iff (H : ℝ[X]) (k : ℝ) :
    H.derivative.derivative = C k ↔
      ∃ d e : ℝ, H = C (k / 2) * X ^ 2 + C d * X + C e := by
  have hq : (C (k / 2) * X ^ 2 : ℝ[X]).derivative = C k * X := by
    apply Polynomial.funext
    intro x
    simp
    ring
  constructor
  · intro h
    let P : ℝ[X] := H.derivative - C k * X
    have hp : P.derivative = 0 := by
      simp only [P, derivative_sub, derivative_C_mul, derivative_X, mul_one, h, sub_self]
    let d := P.coeff 0
    have hd : H.derivative - C k * X = C d := eq_C_of_derivative_eq_zero hp
    let Q : ℝ[X] := H - C (k / 2) * X ^ 2 - C d * X
    have hQ : Q.derivative = 0 := by
      simp only [Q, derivative_sub, hq, derivative_C_mul, derivative_X, mul_one, hd, sub_self]
    have he : H - C (k / 2) * X ^ 2 - C d * X = C (Q.coeff 0) :=
      eq_C_of_derivative_eq_zero hQ
    refine ⟨d, Q.coeff 0, ?_⟩
    linear_combination he
  · rintro ⟨d, e, rfl⟩
    simp only [derivative_add, derivative_C, add_zero, hq,
      derivative_C_mul, derivative_X, mul_one]

/-- The complete constant-shift classification, with the exact allowed quadratic coefficient. -/
theorem gomesDilatonDual_quadratic_rigidity (H : ℝ[X]) (c : ℝ) :
    (∀ x : ℝ, dilatonPotential (-H) x = dilatonPotential H x + c) ↔
      ∃ d e : ℝ, H = C (-c / 2) * X ^ 2 + C d * X + C e := by
  rw [gomesDilatonDual_constant_shift_iff, gomesDilaton_secondDerivative_constant_iff]

end GaloisForLFunctions.HTGeometry

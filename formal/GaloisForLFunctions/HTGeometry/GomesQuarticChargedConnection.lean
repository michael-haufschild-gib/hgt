import GaloisForLFunctions.HTGeometry.GomesDilatonDualShiftRigidity
import GaloisForLFunctions.HTGeometry.GomesQuarticTensorDensity

/-!
# The quartic charge connection and the exact failure of constant oscillator shifts

The common induced-connection experiment extends to the corpus's quartic profiles.
Tensor charge still scales the drift. Duality still reverses factor order, but its correction
is multiplication by `12 a x²`, not a scalar oscillator shift. Both the potential and the
actual Schwartz operators admit a constant dual shift only at the trivial charge.
The surviving positive law is the exact quadratic multiplication commutator.
-/

noncomputable section
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Explicit drift of the quartic charge connection. -/
theorem gomesQuarticDrift_apply (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonDriftCLM (gomesQuarticLogWeight a) ψ x = -2 * (a : ℂ) * x ^ (3 : ℕ) * ψ x := by
  rw [dilatonDriftCLM_apply, gomesQuarticLogWeight_derivative_eval]
  push_cast
  ring

/-- Explicit quartic covariant derivative on the existing Schwartz domain. -/
theorem gomesQuarticSupercharge_apply (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonSuperchargeCLM (gomesQuarticLogWeight a) ψ x = deriv ψ x + 2 * (a : ℂ) * x ^ (3 : ℕ) * ψ x := by
  rw [dilatonSuperchargeCLM_apply, gomesQuarticLogWeight_derivative_eval]
  push_cast
  ring

/-- The other factor retains the same cubic connection term. -/
theorem gomesQuarticAdjointCharge_apply (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonAdjointChargeCLM (gomesQuarticLogWeight a) ψ x = -deriv ψ x + 2 * (a : ℂ) * x ^ (3 : ℕ) * ψ x := by
  rw [dilatonAdjointChargeCLM_apply, gomesQuarticLogWeight_derivative_eval]
  push_cast
  ring

/-- Integer tensor charge multiplies the generating drift exactly. -/
theorem gomesQuarticDrift_charge (b : ℝ) (n : ℤ) :
    dilatonDriftCLM (gomesQuarticTensorLogWeight b n) =
      (n : ℂ) • dilatonDriftCLM (gomesQuarticLogWeight b) := by
  ext ψ x
  simp only [gomesQuarticTensorLogWeight, gomesQuarticDrift_apply, smul_apply,
    smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

/-- The signed quartic profile produces a sextic potential with a quadratic charge term. -/
theorem gomesQuarticPotential_formula (a x : ℝ) :
    dilatonPotential (gomesQuarticLogWeight a) x = 4 * a ^ (2 : ℕ) * x ^ (6 : ℕ) - 6 * a * x ^ (2 : ℕ) := by
  rw [dilatonPotential, gomesQuarticLogWeight_derivative_eval,
    gomesQuarticLogWeight_second_derivative_eval]
  ring

/-- Duality has an exact quadratic spatial correction. -/
theorem gomesQuarticPotential_dual (a x : ℝ) :
    dilatonPotential (gomesQuarticLogWeight (-a)) x =
      dilatonPotential (gomesQuarticLogWeight a) x + 12 * a * x ^ (2 : ℕ) := by
  rw [gomesQuarticPotential_formula, gomesQuarticPotential_formula]
  ring

/-- The quadratic correction holds on every actual Schwartz state. -/
theorem gomesQuarticHamiltonian_dual_apply (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonHamiltonianCLM (gomesQuarticLogWeight (-a)) ψ x =
      dilatonHamiltonianCLM (gomesQuarticLogWeight a) ψ x + 12 * (a : ℂ) * x ^ (2 : ℕ) * ψ x := by
  rw [gomesQuarticLogWeight_neg, gomesDilatonDual_hamiltonian_apply,
    gomesQuarticLogWeight_second_derivative_eval]
  push_cast
  ring

/-- The correction is the literal square-coordinate Schwartz multiplier. -/
theorem gomesQuarticHamiltonian_dual (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesQuarticLogWeight (-a)) ψ =
      dilatonHamiltonianCLM (gomesQuarticLogWeight a) ψ +
        (12 * (a : ℂ)) • mulXCLM (mulXCLM ψ) := by
  ext x
  simp only [gomesQuarticHamiltonian_dual_apply, add_apply, smul_apply, smul_eq_mul, mulXCLM_apply]
  ring

/-- The exact positive replacement for a scalar oscillator commutator is quadratic multiplication. -/
theorem gomesQuarticCharge_commutator (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonSuperchargeCLM (gomesQuarticLogWeight a)
        (dilatonAdjointChargeCLM (gomesQuarticLogWeight a) ψ) -
      dilatonAdjointChargeCLM (gomesQuarticLogWeight a)
        (dilatonSuperchargeCLM (gomesQuarticLogWeight a) ψ) =
      (12 * (a : ℂ)) • mulXCLM (mulXCLM ψ) := by
  ext x
  rw [gomesDilatonDual_commutator_apply, gomesQuarticLogWeight_second_derivative_eval]
  simp only [smul_apply, smul_eq_mul, mulXCLM_apply]
  push_cast
  ring

/-- A constant potential shift is possible only for trivial charge, and that shift is zero. -/
theorem gomesQuarticPotential_constant_shift_iff (a c : ℝ) :
    (∀ x : ℝ, dilatonPotential (gomesQuarticLogWeight (-a)) x =
      dilatonPotential (gomesQuarticLogWeight a) x + c) ↔ a = 0 ∧ c = 0 := by
  simp only [gomesQuarticPotential_dual, add_right_inj]
  constructor
  · intro h
    have hzero := h 0
    have hone := h 1
    simp only [pow_two, mul_zero, mul_one] at hzero hone
    exact ⟨by linarith, hzero.symm⟩
  · rintro ⟨rfl, rfl⟩ x
    ring

/-- The same obstruction holds for the actual operators, not merely their displayed potentials. -/
theorem gomesQuarticHamiltonian_constant_shift_iff (a c : ℝ) :
    (∀ ψ : 𝓢(ℝ, ℂ), dilatonHamiltonianCLM (gomesQuarticLogWeight (-a)) ψ =
      dilatonHamiltonianCLM (gomesQuarticLogWeight a) ψ + (c : ℂ) • ψ) ↔ a = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hcoef (x : ℝ) : 12 * a * x ^ (2 : ℕ) = c := by
      have hx := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ x) (h gaussianSchwartz)
      change dilatonHamiltonianCLM (gomesQuarticLogWeight (-a)) gaussianSchwartz x =
        dilatonHamiltonianCLM (gomesQuarticLogWeight a) gaussianSchwartz x +
          (c : ℂ) * gaussianSchwartz x at hx
      rw [gomesQuarticHamiltonian_dual_apply, add_right_inj] at hx
      have hg : gaussianSchwartz x ≠ 0 := by
        rw [gaussianSchwartz_apply]
        exact Complex.ofReal_ne_zero.mpr (gaussReal_pos x).ne'
      have he := mul_right_cancel₀ hg hx
      exact_mod_cast he
    have hzero := hcoef 0
    have hone := hcoef 1
    simp only [pow_two, mul_zero, mul_one] at hzero hone
    exact ⟨by linarith, hzero.symm⟩
  · rintro ⟨rfl, rfl⟩ ψ
    simp

end GaloisForLFunctions.HTGeometry

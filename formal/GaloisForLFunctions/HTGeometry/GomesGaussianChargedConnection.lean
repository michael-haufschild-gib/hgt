import GaloisForLFunctions.HTGeometry.GomesGaussianTensorDensity

/-!
# The common Gaussian connection and its integer charges

Experimental specialization of the induced-connection principle discussed in arXiv:2404.10461
and the integral tensor charges of arXiv:2509.25276v7 section 5.2. All operators act on the
existing Schwartz domain. Duality reverses the connection and exchanges the two factors;
the Hamiltonian acquires an exact scalar shift. No spectral assumption is supplied.
-/

noncomputable section
open Polynomial
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Explicit drift of the rescaled generating connection. -/
theorem gomesGaussianDrift_apply (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonDriftCLM (gomesGaussianLogWeight a) ψ x =
      -2 * (Real.pi : ℂ) * a * x * ψ x := by
  rw [dilatonDriftCLM_apply, gomesGaussianLogWeight_derivative_eval]
  push_cast
  ring

/-- Covariant derivative on the common Schwartz domain. -/
theorem gomesGaussianSupercharge_apply (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonSuperchargeCLM (gomesGaussianLogWeight a) ψ x =
      deriv ψ x + 2 * (Real.pi : ℂ) * a * x * ψ x := by
  rw [dilatonSuperchargeCLM_apply, gomesGaussianLogWeight_derivative_eval]
  push_cast
  ring

/-- The opposite derivative carries the same connection term. -/
theorem gomesGaussianAdjointCharge_apply (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonAdjointChargeCLM (gomesGaussianLogWeight a) ψ x =
      -deriv ψ x + 2 * (Real.pi : ℂ) * a * x * ψ x := by
  rw [dilatonAdjointChargeCLM_apply, gomesGaussianLogWeight_derivative_eval]
  push_cast
  ring

/-- Tensor charge multiplies the generating drift by its integer weight. -/
theorem gomesGaussianDrift_charge (b : ℝ) (n : ℤ) :
    dilatonDriftCLM (gomesGaussianTensorLogWeight b n) =
      (n : ℂ) • dilatonDriftCLM (gomesGaussianLogWeight b) := by
  ext ψ x
  simp only [gomesGaussianTensorLogWeight, gomesGaussianDrift_apply, smul_apply,
    smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

/-- Tensor addition adds the induced connection terms. -/
theorem gomesGaussianDrift_tensor (b : ℝ) (m n : ℤ) :
    dilatonDriftCLM (gomesGaussianTensorLogWeight b (m + n)) =
      dilatonDriftCLM (gomesGaussianTensorLogWeight b m) +
        dilatonDriftCLM (gomesGaussianTensorLogWeight b n) := by
  rw [gomesGaussianDrift_charge, gomesGaussianDrift_charge, gomesGaussianDrift_charge,
    Int.cast_add, add_smul]

/-- Duality exchanges the two first-order factors with a minus sign. -/
theorem gomesGaussianSupercharge_dual (a : ℝ) :
    dilatonSuperchargeCLM (gomesGaussianLogWeight (-a)) =
      -dilatonAdjointChargeCLM (gomesGaussianLogWeight a) := by
  ext ψ x
  change dilatonSuperchargeCLM (gomesGaussianLogWeight (-a)) ψ x =
    -(dilatonAdjointChargeCLM (gomesGaussianLogWeight a) ψ x)
  rw [gomesGaussianSupercharge_apply, gomesGaussianAdjointCharge_apply, Complex.ofReal_neg]
  ring

/-- The second factor obeys the same dual exchange. -/
theorem gomesGaussianAdjointCharge_dual (a : ℝ) :
    dilatonAdjointChargeCLM (gomesGaussianLogWeight (-a)) =
      -dilatonSuperchargeCLM (gomesGaussianLogWeight a) := by
  ext ψ x
  change dilatonAdjointChargeCLM (gomesGaussianLogWeight (-a)) ψ x =
    -(dilatonSuperchargeCLM (gomesGaussianLogWeight a) ψ x)
  rw [gomesGaussianAdjointCharge_apply, gomesGaussianSupercharge_apply, Complex.ofReal_neg]
  ring

/-- The charged potential contains a quadratic oscillator term and a linear charge shift. -/
theorem gomesGaussianPotential_formula (a x : ℝ) :
    dilatonPotential (gomesGaussianLogWeight a) x =
      4 * Real.pi ^ 2 * a ^ 2 * x ^ 2 - 2 * Real.pi * a := by
  rw [dilatonPotential, gomesGaussianLogWeight_derivative_eval,
    gomesGaussianLogWeight_second_derivative_eval]
  ring

/-- Dual potentials differ by a spatially constant shift. -/
theorem gomesGaussianPotential_dual (a x : ℝ) :
    dilatonPotential (gomesGaussianLogWeight (-a)) x =
      dilatonPotential (gomesGaussianLogWeight a) x + 4 * Real.pi * a := by
  rw [gomesGaussianPotential_formula, gomesGaussianPotential_formula]
  ring

/-- The scalar potential shift lifts to an exact identity of Schwartz operators. -/
theorem gomesGaussianHamiltonian_dual (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesGaussianLogWeight (-a)) ψ =
      dilatonHamiltonianCLM (gomesGaussianLogWeight a) ψ + (4 * (Real.pi : ℂ) * a) • ψ := by
  ext x
  change dilatonHamiltonianCLM (gomesGaussianLogWeight (-a)) ψ x =
    dilatonHamiltonianCLM (gomesGaussianLogWeight a) ψ x + (4 * (Real.pi : ℂ) * a) * ψ x
  rw [dilatonHamiltonianCLM_apply, dilatonHamiltonianCLM_apply, gomesGaussianPotential_dual]
  push_cast
  ring

/-- Duality reverses the order of the two factors. -/
theorem gomesGaussianHamiltonian_dual_factorization (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesGaussianLogWeight (-a)) ψ =
      dilatonSuperchargeCLM (gomesGaussianLogWeight a)
        (dilatonAdjointChargeCLM (gomesGaussianLogWeight a) ψ) := by
  rw [dilatonHamiltonianCLM, ContinuousLinearMap.comp_apply,
    gomesGaussianAdjointCharge_dual, gomesGaussianSupercharge_dual]
  simp

/-- The charge-scaled oscillator commutator follows from the dual shift. -/
theorem gomesGaussianCharge_commutator (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonSuperchargeCLM (gomesGaussianLogWeight a)
        (dilatonAdjointChargeCLM (gomesGaussianLogWeight a) ψ) -
      dilatonAdjointChargeCLM (gomesGaussianLogWeight a)
        (dilatonSuperchargeCLM (gomesGaussianLogWeight a) ψ) =
          (4 * (Real.pi : ℂ) * a) • ψ := by
  rw [← gomesGaussianHamiltonian_dual_factorization, gomesGaussianHamiltonian_dual]
  change _ + _ - dilatonHamiltonianCLM (gomesGaussianLogWeight a) ψ = _
  abel

end GaloisForLFunctions.HTGeometry

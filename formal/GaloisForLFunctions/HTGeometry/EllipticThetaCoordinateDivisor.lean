import GaloisForLFunctions.HTGeometry.EllipticThetaLogCoordinate
import GaloisForLFunctions.HTGeometry.JacobiThetaExactDivisor
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Exact divisor alignment in the exponential theta coordinate

The multiplicative nome orbit is proved to coincide exactly with the odd half-period lattice under
the aligned exponential coordinate. Combined with the exact Jacobi-theta divisor theorem, this
identifies the prospective pole locations of the constructed theta logarithmic kernel with the
zeros of mathlib's analytic `jacobiTheta₂`.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

theorem ellipticThetaCoordinate_eq_exp (τ z : ℂ) :
    ellipticThetaCoordinate τ z =
      Complex.exp (Real.pi * I * (1 + τ + 2 * z)) := by
  rw [ellipticThetaCoordinate]
  rw [mul_add, mul_add, Complex.exp_add, Complex.exp_add]
  have hpi : Complex.exp (Real.pi * I * (1 : ℂ)) = -1 := by
    simp
  rw [hpi]
  simp only [neg_mul]
  ring

theorem ellipticNome_zpow (τ : ℂ) (n : ℤ) :
    ellipticNome τ ^ n = Complex.exp ((n : ℂ) * (2 * Real.pi * I * τ)) := by
  rw [ellipticNome, Complex.exp_int_mul]

theorem ellipticThetaCoordinate_eq_nome_zpow_of_lattice (τ : ℂ) (m n : ℤ) :
    ellipticThetaCoordinate τ
        (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) =
      ellipticNome τ ^ (n + 1) := by
  rw [ellipticThetaCoordinate_eq_exp, ellipticNome_zpow]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m + 1, ?_⟩
  rw [thetaHalfPeriod]
  push_cast
  ring

/-- The full multiplicative nome orbit is exactly the odd half-period lattice. -/
theorem ellipticThetaCoordinate_mem_nomeOrbit_iff_lattice (τ z : ℂ) :
    (∃ N : ℤ, ellipticThetaCoordinate τ z = ellipticNome τ ^ N) ↔
      ∃ m n : ℤ, z = thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ := by
  constructor
  · rintro ⟨N, hN⟩
    rw [ellipticThetaCoordinate_eq_exp, ellipticNome_zpow,
      Complex.exp_eq_exp_iff_exists_int] at hN
    obtain ⟨k, hk⟩ := hN
    refine ⟨k - 1, N - 1, ?_⟩
    have htwoPiI : (2 * Real.pi * I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (mod_cast Real.pi_ne_zero)) I_ne_zero
    apply (mul_left_cancel₀ htwoPiI)
    rw [thetaHalfPeriod]
    push_cast
    linear_combination hk
  · rintro ⟨m, n, rfl⟩
    exact ⟨n + 1, ellipticThetaCoordinate_eq_nome_zpow_of_lattice τ m n⟩

/-- Exact divisor-location bridge: the multiplicative nome orbit is precisely the zero set of
the analytic Jacobi theta function. -/
theorem ellipticThetaCoordinate_mem_nomeOrbit_iff_jacobiTheta₂_zero
    {τ z : ℂ} (hτ : 0 < τ.im) :
    (∃ N : ℤ, ellipticThetaCoordinate τ z = ellipticNome τ ^ N) ↔
      jacobiTheta₂ z τ = 0 := by
  rw [ellipticThetaCoordinate_mem_nomeOrbit_iff_lattice,
    jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ]

end

end GaloisForLFunctions

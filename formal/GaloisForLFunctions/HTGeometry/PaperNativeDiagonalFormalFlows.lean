import GaloisForLFunctions.HTGeometry.PaperTerminatingCore
import GaloisForLFunctions.HTGeometry.PaperLaurentEulerRigidity
import GaloisForLFunctions.HTGeometry.PaperRationalDiagonalRigidity

/-!
# Formal flows for native Laurent and torus clocks

The source formal-flow construction applies to both existing diagonal
derivations. Their exact terminating loci identify their polynomial formal
orbits: Laurent constants and resonant torus polynomials, respectively.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate LaurentDerivation

noncomputable section

/-- On a characteristic-zero field, an everywhere-polynomial derivation flow is trivial. -/
theorem paperFormalField_all_polynomial_iff {k F : Type*} [Field k] [CharZero k]
    [Field F] [CharZero F] [Algebra k F] (D : Derivation k F F) :
    (∀ a, ∃ P : Polynomial F, paperFormalExponential D a = (P : PowerSeries F)) ↔
      D = 0 := by
  rw [paperFormalExponential_all_polynomial_iff, paperLND_field_iff_eq_zero]

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- The full native Laurent Euler clock has a formal flow. -/
def paperLaurentEulerFormalFlow : LaurentSeries K →ₐ[ℂ] PowerSeries (LaurentSeries K) :=
  paperFormalExponential (eulerDerivation (K := K))

/-- The Laurent exponent gives every formal time coefficient explicitly. -/
theorem paperLaurentEulerFormalFlow_coeff (f : LaurentSeries K) (n : ℤ) (m : ℕ) :
    (PowerSeries.coeff m (paperLaurentEulerFormalFlow f)).coeff n =
      ((m.factorial : ℂ)⁻¹) • ((n : K) ^ m * f.coeff n) := by
  rw [paperLaurentEulerFormalFlow, paperFormalExponential_coeff,
    Algebra.smul_def, coeff_algebraMap_mul, paperLaurentEuler_iterate_coeff,
    Algebra.smul_def]

/-- Only coefficient-field constants have polynomial Laurent Euler orbits. -/
theorem paperLaurentEulerFormalFlow_polynomial_iff (f : LaurentSeries K) :
    (∃ P : Polynomial (LaurentSeries K),
      paperLaurentEulerFormalFlow f = (P : PowerSeries (LaurentSeries K))) ↔
      f = HahnSeries.C (f.coeff 0) := by
  rw [paperLaurentEulerFormalFlow, paperFormalExponential_polynomial_iff,
    paperLaurentEuler_terminates_iff]

/-- The Laurent Euler terminating core is exactly the native coefficient-field constants. -/
theorem paperLaurentEulerTerminatingCore_mem_iff (f : LaurentSeries K) :
    f ∈ paperTerminatingCore (eulerDerivation (K := K)) ↔
      f = HahnSeries.C (f.coeff 0) := by
  rw [paperTerminatingCore_mem_iff, paperLaurentEuler_terminates_iff]

variable {r : ℕ}

/-- The native rational torus derivation integrates without imposing resonance. -/
def paperRationalDiagonalFormalFlow (omega : Fin r → ℝ) :
    MvPolynomial (Fin r) ℂ →ₐ[ℂ] PowerSeries (MvPolynomial (Fin r) ℂ) :=
  paperFormalExponential (rationalDiagonalPolynomialDerivation omega)

/-- Every monomial has the exact formal exponential of its native frequency. -/
theorem paperRationalDiagonalFormalFlow_coeff (omega : Fin r → ℝ)
    (f : MvPolynomial (Fin r) ℂ) (s : Fin r →₀ ℕ) (m : ℕ) :
    MvPolynomial.coeff s (PowerSeries.coeff m (paperRationalDiagonalFormalFlow omega f)) =
      ((m.factorial : ℂ)⁻¹) * paperRationalDiagonalWeight omega s ^ m *
        MvPolynomial.coeff s f := by
  simp only [paperRationalDiagonalFormalFlow, paperFormalExponential_coeff,
    MvPolynomial.coeff_smul, paperRationalDiagonal_iterate_coeff, smul_eq_mul]
  rw [mul_assoc]

/-- Polynomial formal orbits are exactly polynomials supported on resonant monomials. -/
theorem paperRationalDiagonalFormalFlow_polynomial_iff (omega : Fin r → ℝ)
    (f : MvPolynomial (Fin r) ℂ) :
    (∃ P : Polynomial (MvPolynomial (Fin r) ℂ),
      paperRationalDiagonalFormalFlow omega f = (P : PowerSeries (MvPolynomial (Fin r) ℂ))) ↔
      ∀ s, MvPolynomial.coeff s f ≠ 0 → paperRationalDiagonalWeight omega s = 0 := by
  rw [paperRationalDiagonalFormalFlow, paperFormalExponential_polynomial_iff,
    paperRationalDiagonal_terminates_iff, paperRationalDiagonal_kernel_iff]

/-- A finite torus orbit is already fixed: no nonconstant polynomial time motion survives. -/
theorem paperRationalDiagonalFormalFlow_polynomial_iff_fixed (omega : Fin r → ℝ)
    (f : MvPolynomial (Fin r) ℂ) :
    (∃ P : Polynomial (MvPolynomial (Fin r) ℂ),
      paperRationalDiagonalFormalFlow omega f = (P : PowerSeries (MvPolynomial (Fin r) ℂ))) ↔
      paperRationalDiagonalFormalFlow omega f = PowerSeries.C f := by
  rw [paperRationalDiagonalFormalFlow, paperFormalExponential_polynomial_iff,
    paperRationalDiagonal_terminates_iff, paperFormalExponential_fixed_iff]

/-- The same resonance law identifies the maximal terminating torus subalgebra. -/
theorem paperRationalDiagonalTerminatingCore_mem_iff (omega : Fin r → ℝ)
    (f : MvPolynomial (Fin r) ℂ) :
    f ∈ paperTerminatingCore (rationalDiagonalPolynomialDerivation omega) ↔
      ∀ s, MvPolynomial.coeff s f ≠ 0 → paperRationalDiagonalWeight omega s = 0 := by
  rw [paperTerminatingCore_mem_iff, paperRationalDiagonal_terminates_iff,
    paperRationalDiagonal_kernel_iff]

end

end GaloisForLFunctions.HTGeometry

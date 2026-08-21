/-
# Chen--Gupta--Li class-I bounded-coefficient normalization

Section 12.3 rescales each dyadic class-I detector block to coefficients
`a_n` with `|a_n| ≤ 1` before applying its large-value theorems.  This module
constructs a closed finite normalization from the literal detector vector,
proves the exact polynomial scaling relation, and supplies the corresponding
baseline large-value count.  The asymptotic choice `varpi ≍ N^{-ε}` and CGL's
refined large-value estimate remain later analytic layers.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassILargeValues

open Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- A deterministic positive normalization for the exact finite class-I
coefficient vector. -/
def cglClassIDyadicCoefficientScale (X N : ℕ) : ℝ :=
  (1 + ‖cglClassIDyadicDetectorCoefficients X N‖)⁻¹

/-- The normalized finite coefficient vector used by the class-I
Dirichlet polynomial. -/
def cglClassIDyadicScaledCoefficients (X N : ℕ) : EuclideanSpace ℂ (Fin N) :=
  (cglClassIDyadicCoefficientScale X N : ℂ) • cglClassIDyadicDetectorCoefficients X N

/-- The deterministic normalization makes the full coefficient vector have
norm at most one. -/
theorem norm_cglClassIDyadicScaledCoefficients_le_one (X N : ℕ) :
    ‖cglClassIDyadicScaledCoefficients X N‖ ≤ 1 := by
  let A : ℝ := ‖cglClassIDyadicDetectorCoefficients X N‖
  have hA : 0 ≤ A := norm_nonneg _
  have hpos : 0 < 1 + A := by linarith
  have hscale : 0 ≤ cglClassIDyadicCoefficientScale X N := by
    simp only [cglClassIDyadicCoefficientScale]
    positivity
  change ‖(cglClassIDyadicCoefficientScale X N : ℂ) •
    cglClassIDyadicDetectorCoefficients X N‖ ≤ 1
  rw [norm_smul]
  simp only [Complex.norm_real]
  rw [Real.norm_of_nonneg hscale]
  change cglClassIDyadicCoefficientScale X N * A ≤ 1
  rw [cglClassIDyadicCoefficientScale]
  calc
    (1 + A)⁻¹ * A = A / (1 + A) := by ring
    _ ≤ 1 := (div_le_one₀ hpos).mpr (by linarith)

/-- Every normalized class-I coefficient has norm at most one. -/
theorem norm_cglClassIDyadicScaledCoefficient_le_one (X N : ℕ) (j : Fin N) :
    ‖(cglClassIDyadicScaledCoefficients X N) j‖ ≤ 1 := by
  have hvector := norm_cglClassIDyadicScaledCoefficients_le_one X N
  have hsq : ‖(cglClassIDyadicScaledCoefficients X N) j‖ ^ 2 ≤
      ‖cglClassIDyadicScaledCoefficients X N‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.single_le_sum (fun i hi => sq_nonneg
      ‖(cglClassIDyadicScaledCoefficients X N) i‖) (Finset.mem_univ _)
  nlinarith [norm_nonneg ((cglClassIDyadicScaledCoefficients X N) j),
    norm_nonneg (cglClassIDyadicScaledCoefficients X N)]

/-- The class-I detector polynomial with the normalized coefficient vector. -/
def cglClassIDyadicScaledDetectorPolynomial (X N q : ℕ)
    (w : CGLCharacterDyadicRowData q) : ℂ :=
  cglCharacterDyadicPolynomial N q w (cglClassIDyadicScaledCoefficients X N)

/-- The normalized detector is exactly the positive scale times the literal
class-I detector polynomial. -/
theorem cglClassIDyadicScaledDetectorPolynomial_eq_scale_mul (X N q : ℕ)
    (w : CGLCharacterDyadicRowData q) :
    cglClassIDyadicScaledDetectorPolynomial X N q w =
      (cglClassIDyadicCoefficientScale X N : ℂ) *
        cglClassIDyadicDetectorPolynomial X N q w := by
  simp only [cglClassIDyadicScaledDetectorPolynomial,
    cglCharacterDyadicPolynomial, cglClassIDyadicScaledCoefficients,
    cglClassIDyadicDetectorPolynomial, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Rows whose normalized class-I detector exceeds its nonnegative threshold. -/
def cglClassIDyadicScaledLargeValues (X N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (V : NNReal) : Finset (Fin R) :=
  cglCharacterDyadicLargeValues N q R w (cglClassIDyadicScaledCoefficients X N) V

/-- Membership in the normalized class-I large-value packet is exactly its
literal detector-threshold inequality. -/
theorem mem_cglClassIDyadicScaledLargeValues_iff (X N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (V : NNReal) (r : Fin R) :
    r ∈ cglClassIDyadicScaledLargeValues X N q R w V ↔
      (V : ℝ) ≤ ‖cglClassIDyadicScaledDetectorPolynomial X N q (w r)‖ := by
  simp only [cglClassIDyadicScaledLargeValues, cglCharacterDyadicLargeValues,
    Finset.mem_filter, Finset.mem_univ, true_and,
    cglClassIDyadicScaledDetectorPolynomial]

/-- Closed baseline large-value estimate for the normalized class-I packet. -/
theorem card_cglClassIDyadicScaledLargeValues_mul_sq_le (X N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (V : NNReal) :
    ((cglClassIDyadicScaledLargeValues X N q R w V).card : ℝ) * (V : ℝ) ^ 2 ≤
      (R : ℝ) * (N : ℝ) := by
  calc
    ((cglClassIDyadicScaledLargeValues X N q R w V).card : ℝ) * (V : ℝ) ^ 2 ≤
        (R : ℝ) * (N : ℝ) * ‖cglClassIDyadicScaledCoefficients X N‖ ^ 2 :=
      card_cglCharacterDyadicLargeValues_mul_sq_le N q R w
        (cglClassIDyadicScaledCoefficients X N) V
    _ ≤ (R : ℝ) * (N : ℝ) * 1 := by
      gcongr
      nlinarith [norm_nonneg (cglClassIDyadicScaledCoefficients X N),
        norm_cglClassIDyadicScaledCoefficients_le_one X N]
    _ = (R : ℝ) * (N : ℝ) := by ring

end RHTower

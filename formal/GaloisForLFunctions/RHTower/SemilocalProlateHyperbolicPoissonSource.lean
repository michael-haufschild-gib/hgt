import GaloisForLFunctions.RHTower.SemilocalProlateOddHarmonicActivation
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Hyperbolic Poisson structure of the semilocal prolate source

The exact Meixner--Poisson resummation uses the parameter

`a(s) = (1 - s²) / (1 + s²)`.

This file formalizes the source-specific algebra behind that resummation:

* factorization of the bivariate Meixner denominator;
* the multiplicative-to-hyperbolic group law `a(st) = a(s) ⊕ a(t)`;
* the exact half-density normalization `1-a(s)²`;
* positivity, strict positivity, and compression stability of the resolved Poisson Gram.

All statements are unconditional.  The remaining Route-J problem is analytic: uniform discrete
regularity of the source finite sections through the four-radius stencil.
-/

noncomputable section

open scoped Matrix

namespace RHTower.SemilocalProlateHyperbolicPoissonSource

/-- Hyperbolic translation parameter selected by the exact Meixner source kernel. -/
def sourceHyperbolicParameter (s : ℝ) : ℝ :=
  (1 - s ^ 2) / (1 + s ^ 2)

/-- Polynomial under the square root in the exact bivariate source generating function. -/
def sourceMeixnerDenominator (s x y : ℝ) : ℝ :=
  (1 - x) * (1 - y) + s ^ 2 * (1 + x) * (1 + y)

/-- Linear fractional factor exposed by the hyperbolic parameter. -/
def sourceReflectedLinearFactor (s x y : ℝ) : ℝ :=
  (1 - sourceHyperbolicParameter s * x) -
    (sourceHyperbolicParameter s - x) * y

theorem one_add_sq_ne_zero (s : ℝ) :
    1 + s ^ 2 ≠ 0 := by
  positivity

/-- Exact factorization of the bivariate Meixner denominator. -/
theorem sourceMeixnerDenominator_factor (s x y : ℝ) :
    sourceMeixnerDenominator s x y =
      (1 + s ^ 2) * sourceReflectedLinearFactor s x y := by
  unfold sourceMeixnerDenominator sourceReflectedLinearFactor sourceHyperbolicParameter
  field_simp [one_add_sq_ne_zero]
  ring

/-- The disk-translation normalization is exactly the source half-density factor. -/
theorem one_sub_sourceHyperbolicParameter_sq (s : ℝ) :
    1 - sourceHyperbolicParameter s ^ 2 =
      (2 * s / (1 + s ^ 2)) ^ 2 := by
  unfold sourceHyperbolicParameter
  field_simp [one_add_sq_ne_zero]
  ring

private theorem one_add_parameter_mul_parameter (s t : ℝ) :
    1 + sourceHyperbolicParameter s * sourceHyperbolicParameter t =
      2 * (1 + (s * t) ^ 2) / ((1 + s ^ 2) * (1 + t ^ 2)) := by
  unfold sourceHyperbolicParameter
  field_simp [one_add_sq_ne_zero]
  ring

theorem one_add_parameter_mul_parameter_ne_zero (s t : ℝ) :
    1 + sourceHyperbolicParameter s * sourceHyperbolicParameter t ≠ 0 := by
  rw [one_add_parameter_mul_parameter]
  positivity

/-- Multiplication of Lambert scales is addition in the hyperbolic translation group. -/
theorem sourceHyperbolicParameter_mul (s t : ℝ) :
    sourceHyperbolicParameter (s * t) =
      (sourceHyperbolicParameter s + sourceHyperbolicParameter t) /
        (1 + sourceHyperbolicParameter s * sourceHyperbolicParameter t) := by
  rw [one_add_parameter_mul_parameter]
  unfold sourceHyperbolicParameter
  field_simp [one_add_sq_ne_zero]
  ring

theorem sourceHyperbolicParameter_one :
    sourceHyperbolicParameter 1 = 0 := by
  norm_num [sourceHyperbolicParameter]

theorem sourceHyperbolicParameter_pos_of_lt_one {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 < sourceHyperbolicParameter s := by
  unfold sourceHyperbolicParameter
  have hsSq : s ^ 2 < 1 := by nlinarith [mul_self_lt_mul_self hs0 hs1]
  exact div_pos (sub_pos.mpr hsSq) (by positivity)

theorem sourceHyperbolicParameter_lt_one_of_pos {s : ℝ} (hs : 0 < s) :
    sourceHyperbolicParameter s < 1 := by
  unfold sourceHyperbolicParameter
  apply (div_lt_one (by positivity : 0 < 1 + s ^ 2)).mpr
  nlinarith [sq_pos_of_pos hs]

/-- Finite-dimensional resolved Poisson Gram from a resolvent frame. -/
def sourceResolvedPoissonMatrix {n : Type*} [Fintype n]
    (q : ℝ) (R : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 - q) • (R * Rᴴ)

/-- The exact Poisson resolvent factor is positive semidefinite for `q ≤ 1`. -/
theorem sourceResolvedPoissonMatrix_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ) (R : Matrix n n ℝ) (hq : q ≤ 1) :
    (sourceResolvedPoissonMatrix q R).PosSemidef := by
  unfold sourceResolvedPoissonMatrix
  exact (Matrix.posSemidef_self_mul_conjTranspose R).smul (sub_nonneg.mpr hq)

/-- An invertible resolvent frame makes the Poisson factor strictly positive. -/
theorem sourceResolvedPoissonMatrix_posDef
    {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ) (R : Matrix n n ℝ) (hq : q < 1) (hR : IsUnit R) :
    (sourceResolvedPoissonMatrix q R).PosDef := by
  unfold sourceResolvedPoissonMatrix
  have hInjective : Function.Injective R.vecMul :=
    Matrix.vecMul_injective_of_isUnit hR
  exact (Matrix.PosDef.mul_conjTranspose_self R hInjective).smul (sub_pos.mpr hq)

/-- Every finite coordinate compression of the resolved source remains positive semidefinite. -/
theorem sourceResolvedPoissonMatrix_compression_posSemidef
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (q : ℝ) (R : Matrix n n ℝ) (Q : Matrix m n ℝ) (hq : q ≤ 1) :
    (Q * sourceResolvedPoissonMatrix q R * Qᴴ).PosSemidef := by
  have h := sourceResolvedPoissonMatrix_posSemidef q R hq
  simpa [Matrix.mul_assoc] using h.conjTranspose_mul_mul_same Qᴴ

/-- Literal four-index determinant stencil is a difference of two parity-boundary increments. -/
theorem fourIndexStencil_eq_boundaryIncrementDifference
    (L : ℤ → ℝ) (n : ℤ) :
    L (n + 1) + L (n - 2) - L n - L (n - 1) =
      (L (n + 1) - L (n - 1)) - (L n - L (n - 2)) := by
  ring

end RHTower.SemilocalProlateHyperbolicPoissonSource

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Centroid gauge for finite Hilbert metrics

This module proves the exact finite Hilbert-space variance identities needed to remove the
arbitrary choice of origin from feature-kernel determinant formulas.  The centroid is defined for
an arbitrary nonempty finite index type.  Its centered energy is both the unique translation
minimum and a function of pairwise squared distances alone.
-/

open scoped BigOperators RealInnerProductSpace

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The equal-weight centroid of a nonempty finite Hilbert family. -/
def hilbertCentroid (x : ι → E) : E :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, x i

/-- Multiplication by the cardinality cancels the centroid average. -/
theorem card_smul_hilbertCentroid (x : ι → E) :
    (Fintype.card ι : ℝ) • hilbertCentroid x = ∑ i, x i := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hilbertCentroid, smul_smul, hn]

/-- Centered Hilbert vectors have zero total displacement. -/
theorem sum_sub_hilbertCentroid (x : ι → E) :
    ∑ i, (x i - hilbertCentroid x) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← card_smul_hilbertCentroid x]
  simp

/-- **Hilbert centroid translation law.**  Moving the origin from the centroid to `a` adds
exactly the cardinality times the squared displacement of the origin. -/
theorem sum_norm_sub_sq_eq_centered_add_card_mul (x : ι → E) (a : E) :
    ∑ i, ‖x i - a‖ ^ 2 =
      (∑ i, ‖x i - hilbertCentroid x‖ ^ 2) +
        (Fintype.card ι : ℝ) * ‖hilbertCentroid x - a‖ ^ 2 := by
  have hdecomp : ∀ i, x i - a =
      (x i - hilbertCentroid x) + (hilbertCentroid x - a) := by
    intro i
    abel
  simp_rw [hdecomp, norm_add_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← real_inner_sum_left, sum_sub_hilbertCentroid]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- **Metric energy law.**  The total ordered pairwise squared distance is twice the cardinality
times the centered energy.  Thus the centered energy depends only on the finite metric. -/
theorem sum_pairwise_norm_sub_sq_eq_two_card_mul_centered (x : ι → E) :
    ∑ i, ∑ j, ‖x i - x j‖ ^ 2 =
      2 * (Fintype.card ι : ℝ) *
        ∑ i, ‖x i - hilbertCentroid x‖ ^ 2 := by
  have hsub : ∀ i j, x i - x j =
      (x i - hilbertCentroid x) - (x j - hilbertCentroid x) := by
    intro i j
    abel
  simp_rw [hsub, norm_sub_sq_real]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← real_inner_sum_right, sum_sub_hilbertCentroid]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Exponential centroid-gauge factorization.**  The translation-dependent exponential
feature gauge splits into the intrinsic centered factor and one universal displacement factor.
This is the scalar gauge identity used by Gaussian distance determinants. -/
theorem exp_two_mul_sum_norm_sub_sq_eq_centroid_factor
    (x : ι → E) (a : E) (t : ℝ) :
    Real.exp (2 * t * ∑ i, ‖x i - a‖ ^ 2) =
      Real.exp
          (2 * t * (Fintype.card ι : ℝ) * ‖hilbertCentroid x - a‖ ^ 2) *
        Real.exp (2 * t * ∑ i, ‖x i - hilbertCentroid x‖ ^ 2) := by
  rw [sum_norm_sub_sq_eq_centered_add_card_mul]
  rw [show 2 * t *
        ((∑ i, ‖x i - hilbertCentroid x‖ ^ 2) +
          (Fintype.card ι : ℝ) * ‖hilbertCentroid x - a‖ ^ 2) =
      2 * t * (Fintype.card ι : ℝ) * ‖hilbertCentroid x - a‖ ^ 2 +
        2 * t * ∑ i, ‖x i - hilbertCentroid x‖ ^ 2 by ring]
  exact Real.exp_add _ _

section GaussianGauge

/-- The Gaussian distance matrix of a finite Hilbert family at inverse squared bandwidth `t`. -/
def gaussianDistanceMatrix (x : ι → E) (t : ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.exp (-t * ‖x i - x j‖ ^ 2)

/-- The exponential inner-product feature matrix formed about an arbitrary origin `a`. -/
def exponentialInnerMatrix (x : ι → E) (a : E) (t : ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.exp (2 * t * inner ℝ (x i - a) (x j - a))

/-- The diagonal change of gauge from the Gaussian distance matrix to its exponential
inner-product feature matrix. -/
def gaussianGaugeDiagonal (x : ι → E) (a : E) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i => Real.exp (-t * ‖x i - a‖ ^ 2)

/-- Exact diagonal factorization of a Gaussian distance matrix about any Hilbert-space origin. -/
theorem gaussianDistanceMatrix_eq_diagonal_mul_inner_mul_diagonal
    (x : ι → E) (a : E) (t : ℝ) :
    gaussianDistanceMatrix x t =
      gaussianGaugeDiagonal x a t * exponentialInnerMatrix x a t *
        gaussianGaugeDiagonal x a t := by
  classical
  ext i j
  simp [gaussianDistanceMatrix, gaussianGaugeDiagonal, exponentialInnerMatrix,
    Matrix.mul_apply, norm_sub_sq_real]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The product of the Gaussian diagonal gauge is the exponential of its total exponent. -/
theorem prod_exp_neg_mul_norm_sub_sq
    (x : ι → E) (a : E) (t : ℝ) :
    ∏ i, Real.exp (-t * ‖x i - a‖ ^ 2) =
      Real.exp (-t * ∑ i, ‖x i - a‖ ^ 2) := by
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- Determinant form of the Gaussian diagonal factorization. -/
theorem gaussianDistanceMatrix_det_eq_exp_mul_exponentialInnerMatrix_det
    (x : ι → E) (a : E) (t : ℝ) :
    (gaussianDistanceMatrix x t).det =
      Real.exp (-2 * t * ∑ i, ‖x i - a‖ ^ 2) *
        (exponentialInnerMatrix x a t).det := by
  classical
  rw [gaussianDistanceMatrix_eq_diagonal_mul_inner_mul_diagonal x a t,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    prod_exp_neg_mul_norm_sub_sq, prod_exp_neg_mul_norm_sub_sq]
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Corrected Gaussian determinant identity.**  Multiplication by the exact origin energy
turns the metric Gaussian determinant into the exponential inner-product determinant. -/
theorem exp_energy_mul_gaussianDistanceMatrix_det
    (x : ι → E) (a : E) (t : ℝ) :
    Real.exp (2 * t * ∑ i, ‖x i - a‖ ^ 2) *
        (gaussianDistanceMatrix x t).det =
      (exponentialInnerMatrix x a t).det := by
  classical
  rw [gaussianDistanceMatrix_det_eq_exp_mul_exponentialInnerMatrix_det]
  rw [← mul_assoc, ← Real.exp_add]
  simp

/-- **Gaussian centroid-gauge law.**  Changing the Fock origin away from the centroid multiplies
the corrected determinant by one universal positive exponential.  No source-specific structure
or finite-dimensional ambient-space hypothesis is used. -/
theorem exponentialInnerMatrix_det_eq_centroid_factor
    (x : ι → E) (a : E) (t : ℝ) :
    (exponentialInnerMatrix x a t).det =
      Real.exp
          (2 * t * (Fintype.card ι : ℝ) * ‖hilbertCentroid x - a‖ ^ 2) *
        (exponentialInnerMatrix x (hilbertCentroid x) t).det := by
  classical
  calc
    (exponentialInnerMatrix x a t).det =
        Real.exp (2 * t * ∑ i, ‖x i - a‖ ^ 2) *
          (gaussianDistanceMatrix x t).det :=
      (exp_energy_mul_gaussianDistanceMatrix_det x a t).symm
    _ = (Real.exp
          (2 * t * (Fintype.card ι : ℝ) * ‖hilbertCentroid x - a‖ ^ 2) *
        Real.exp (2 * t * ∑ i, ‖x i - hilbertCentroid x‖ ^ 2)) *
          (gaussianDistanceMatrix x t).det := by
      rw [exp_two_mul_sum_norm_sub_sq_eq_centroid_factor]
    _ = Real.exp
          (2 * t * (Fintype.card ι : ℝ) * ‖hilbertCentroid x - a‖ ^ 2) *
        (exponentialInnerMatrix x (hilbertCentroid x) t).det := by
      rw [mul_assoc,
        exp_energy_mul_gaussianDistanceMatrix_det x (hilbertCentroid x) t]

end GaussianGauge

end

end GaloisForLFunctions.HilbertMetric

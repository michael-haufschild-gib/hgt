import GaloisForLFunctions.HilbertMetric.GaussianFock
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

local instance : DecidableEq ι := Classical.decEq ι

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
  rw [Finset.sum_sub_distrib, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, Finset.card_univ,
    card_smul_hilbertCentroid x, sub_self]

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
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← sum_inner, sum_sub_hilbertCentroid]
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
  have hexpand (i j : ι) :
      ‖x i - x j‖ ^ 2 =
        ‖x i - hilbertCentroid x‖ ^ 2 -
          2 * inner ℝ (x i - hilbertCentroid x) (x j - hilbertCentroid x) +
            ‖x j - hilbertCentroid x‖ ^ 2 := by
    rw [hsub, norm_sub_sq_real]
  have hcross (i : ι) :
      ∑ j, 2 * inner ℝ (x i - hilbertCentroid x) (x j - hilbertCentroid x) = 0 := by
    rw [← Finset.mul_sum, ← inner_sum, sum_sub_hilbertCentroid]
    simp
  have hinner (i : ι) :
      ∑ j, (‖x i - hilbertCentroid x‖ ^ 2 -
          2 * inner ℝ (x i - hilbertCentroid x) (x j - hilbertCentroid x) +
            ‖x j - hilbertCentroid x‖ ^ 2) =
        (Fintype.card ι : ℝ) * ‖x i - hilbertCentroid x‖ ^ 2 +
          ∑ j, ‖x j - hilbertCentroid x‖ ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross]
    simp [Finset.sum_const, nsmul_eq_mul]
  calc
    _ = ∑ i, ∑ j, (‖x i - hilbertCentroid x‖ ^ 2 -
          2 * inner ℝ (x i - hilbertCentroid x) (x j - hilbertCentroid x) +
            ‖x j - hilbertCentroid x‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hexpand i j
    _ = ∑ i, ((Fintype.card ι : ℝ) * ‖x i - hilbertCentroid x‖ ^ 2 +
          ∑ j, ‖x j - hilbertCentroid x‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hinner i
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
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
def gaussianGaugeDiagonal (x : ι → E) (a : E) (t : ℝ) : Matrix ι ι ℝ := by
  classical
  exact Matrix.diagonal fun i => Real.exp (-t * ‖x i - a‖ ^ 2)

omit [Nonempty ι] in
/-- Exact diagonal factorization of a Gaussian distance matrix about any Hilbert-space origin. -/
theorem gaussianDistanceMatrix_eq_diagonal_mul_inner_mul_diagonal
    (x : ι → E) (a : E) (t : ℝ) :
    gaussianDistanceMatrix x t =
      gaussianGaugeDiagonal x a t * exponentialInnerMatrix x a t *
        gaussianGaugeDiagonal x a t := by
  classical
  ext i j
  simp only [gaussianDistanceMatrix, gaussianGaugeDiagonal]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [exponentialInnerMatrix]
  simp only [norm_sub_sq_real]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [inner_sub_left, inner_sub_right, real_inner_comm,
    real_inner_self_eq_norm_sq]
  ring_nf

omit [Nonempty ι] [InnerProductSpace ℝ E] in
/-- The product of the Gaussian diagonal gauge is the exponential of its total exponent. -/
theorem prod_exp_neg_mul_norm_sub_sq
    (x : ι → E) (a : E) (t : ℝ) :
    ∏ i, Real.exp (-t * ‖x i - a‖ ^ 2) =
      Real.exp (-t * ∑ i, ‖x i - a‖ ^ 2) := by
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

omit [Nonempty ι] in
/-- Determinant form of the Gaussian diagonal factorization. -/
theorem gaussianDistanceMatrix_det_eq_exp_mul_exponentialInnerMatrix_det
    (x : ι → E) (a : E) (t : ℝ) :
    (gaussianDistanceMatrix x t).det =
      Real.exp (-2 * t * ∑ i, ‖x i - a‖ ^ 2) *
        (exponentialInnerMatrix x a t).det := by
  classical
  rw [gaussianDistanceMatrix_eq_diagonal_mul_inner_mul_diagonal x a t,
    Matrix.det_mul, Matrix.det_mul]
  simp only [gaussianGaugeDiagonal, Matrix.det_diagonal]
  simp only [prod_exp_neg_mul_norm_sub_sq]
  calc
    _ = (Real.exp (-t * ∑ i, ‖x i - a‖ ^ 2) *
          Real.exp (-t * ∑ i, ‖x i - a‖ ^ 2)) *
        (exponentialInnerMatrix x a t).det := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

omit [Nonempty ι] in
/-- **Corrected Gaussian determinant identity.**  Multiplication by the exact origin energy
turns the metric Gaussian determinant into the exponential inner-product determinant. -/
theorem exp_energy_mul_gaussianDistanceMatrix_det
    (x : ι → E) (a : E) (t : ℝ) :
    Real.exp (2 * t * ∑ i, ‖x i - a‖ ^ 2) *
        (gaussianDistanceMatrix x t).det =
      (exponentialInnerMatrix x a t).det := by
  classical
  rw [gaussianDistanceMatrix_det_eq_exp_mul_exponentialInnerMatrix_det x a t]
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

/-! ### Canonical metric correction and the universal three-scale law -/

/-- The centroid-corrected Gaussian determinant.  The centroid-energy identity above shows that
this scalar depends only on the finite Hilbert metric, despite its centered presentation. -/
def gaussianCorrectedDeterminant (x : ι → E) (t : ℝ) : ℝ := by
  classical
  exact Real.exp (2 * t * ∑ i, ‖x i - hilbertCentroid x‖ ^ 2) *
    (gaussianDistanceMatrix x t).det

omit [Nonempty ι] in
/-- The corrected metric determinant is exactly the exponential inner-product determinant of
the centered configuration. -/
theorem gaussianCorrectedDeterminant_eq_hilbertExponentialInnerMatrix_det
    (x : ι → E) (t : ℝ) :
    gaussianCorrectedDeterminant x t =
      (hilbertExponentialInnerMatrix (fun i => x i - hilbertCentroid x) t).det := by
  classical
  unfold gaussianCorrectedDeterminant
  rw [exp_energy_mul_gaussianDistanceMatrix_det x (hilbertCentroid x) t]
  rfl

omit [Nonempty ι] in
/-- **Centroid-corrected Gaussian determinant law.**  The canonical metric determinant is
multiplicatively midpoint log-convex at all nonnegative scales. -/
theorem gaussianCorrectedDeterminant_mul_sq_le
    (x : ι → E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    gaussianCorrectedDeterminant x (a * b) ^ 2 ≤
      gaussianCorrectedDeterminant x (a ^ 2) *
        gaussianCorrectedDeterminant x (b ^ 2) := by
  classical
  rw [gaussianCorrectedDeterminant_eq_hilbertExponentialInnerMatrix_det]
  rw [gaussianCorrectedDeterminant_eq_hilbertExponentialInnerMatrix_det]
  rw [gaussianCorrectedDeterminant_eq_hilbertExponentialInnerMatrix_det]
  exact hilbertExponentialInnerMatrix_det_mul_sq_le
    (fun i => x i - hilbertCentroid x) a b ha hb

omit [Nonempty ι] in
/-- Expanded form of the canonical law, exposing the exact metric-energy correction. -/
theorem exp_centroidEnergy_mul_gaussianDistanceMatrix_det_mul_sq_le
    (x : ι → E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.exp (2 * (a * b) * ∑ i, ‖x i - hilbertCentroid x‖ ^ 2) *
        (gaussianDistanceMatrix x (a * b)).det) ^ 2 ≤
      (Real.exp (2 * a ^ 2 * ∑ i, ‖x i - hilbertCentroid x‖ ^ 2) *
          (gaussianDistanceMatrix x (a ^ 2)).det) *
        (Real.exp (2 * b ^ 2 * ∑ i, ‖x i - hilbertCentroid x‖ ^ 2) *
          (gaussianDistanceMatrix x (b ^ 2)).det) := by
  exact gaussianCorrectedDeterminant_mul_sq_le x a b ha hb

omit [Nonempty ι] in
/-- **Raw Gaussian three-scale law.**  Removing the centroid correction exposes the sharp
universal energy defect `exp (2 * (a - b)^2 * E)`. -/
theorem gaussianDistanceMatrix_det_mul_sq_le
    (x : ι → E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (gaussianDistanceMatrix x (a * b)).det ^ 2 ≤
      Real.exp
          (2 * (a - b) ^ 2 * ∑ i, ‖x i - hilbertCentroid x‖ ^ 2) *
        (gaussianDistanceMatrix x (a ^ 2)).det *
          (gaussianDistanceMatrix x (b ^ 2)).det := by
  classical
  let energy : ℝ := ∑ i, ‖x i - hilbertCentroid x‖ ^ 2
  have h := exp_centroidEnergy_mul_gaussianDistanceMatrix_det_mul_sq_le
    x a b ha hb
  change
    (Real.exp (2 * (a * b) * energy) *
        (gaussianDistanceMatrix x (a * b)).det) ^ 2 ≤
      (Real.exp (2 * a ^ 2 * energy) *
          (gaussianDistanceMatrix x (a ^ 2)).det) *
        (Real.exp (2 * b ^ 2 * energy) *
          (gaussianDistanceMatrix x (b ^ 2)).det) at h
  have hexp :
      Real.exp (4 * (a * b) * energy) *
          Real.exp (2 * (a - b) ^ 2 * energy) =
        Real.exp (2 * a ^ 2 * energy) *
          Real.exp (2 * b ^ 2 * energy) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hmul :
      Real.exp (4 * (a * b) * energy) *
          (gaussianDistanceMatrix x (a * b)).det ^ 2 ≤
        Real.exp (4 * (a * b) * energy) *
          (Real.exp (2 * (a - b) ^ 2 * energy) *
            (gaussianDistanceMatrix x (a ^ 2)).det *
              (gaussianDistanceMatrix x (b ^ 2)).det) := by
    calc
      _ = (Real.exp (2 * (a * b) * energy) *
          (gaussianDistanceMatrix x (a * b)).det) ^ 2 := by
        rw [mul_pow]
        congr 1
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := h
      _ = _ := by
        calc
          _ = (Real.exp (2 * a ^ 2 * energy) *
                Real.exp (2 * b ^ 2 * energy)) *
              ((gaussianDistanceMatrix x (a ^ 2)).det *
                (gaussianDistanceMatrix x (b ^ 2)).det) := by ring
          _ = (Real.exp (4 * (a * b) * energy) *
                Real.exp (2 * (a - b) ^ 2 * energy)) *
              ((gaussianDistanceMatrix x (a ^ 2)).det *
                (gaussianDistanceMatrix x (b ^ 2)).det) := by rw [hexp]
          _ = _ := by ring
  exact le_of_mul_le_mul_left hmul (Real.exp_pos (4 * (a * b) * energy))

end GaussianGauge

end

end GaloisForLFunctions.HilbertMetric

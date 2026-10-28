import Mathlib.Analysis.Matrix.Spectrum

/-!
# A finite Hermitian residual finds an eigenvalue

Parseval in the actual orthonormal eigenbasis converts a strict residual bound
into an eigenvalue in the prescribed interval.
-/

noncomputable section

open Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-- A residual smaller than `δ` times the vector norm forces an actual eigenvalue
within `δ` of the trial energy. The strict inequality also excludes the zero vector. -/
theorem exists_eigenvalue_abs_sub_lt_of_residual_sq_lt
    {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℝ}
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ I) (μ : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hres : ‖Matrix.toEuclideanLin A x - μ • x‖ ^ 2 < δ ^ 2 * ‖x‖ ^ 2) :
    ∃ i, |hA.eigenvalues i - μ| < δ := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have heig (i : I) : Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have hcoeff (i : I) :
      ⟪Matrix.toEuclideanLin A x - μ • x, hA.eigenvectorBasis i⟫ =
        (hA.eigenvalues i - μ) * ⟪x, hA.eigenvectorBasis i⟫ := by
    rw [inner_sub_left, real_inner_smul_left, hs x (hA.eigenvectorBasis i),
      heig, real_inner_smul_right]
    ring
  by_contra hn
  push Not at hn
  have hsum : δ ^ 2 * ‖x‖ ^ 2 ≤
      ‖Matrix.toEuclideanLin A x - μ • x‖ ^ 2 := by
    rw [← hA.eigenvectorBasis.sum_sq_inner_left x,
      ← hA.eigenvectorBasis.sum_sq_inner_left (Matrix.toEuclideanLin A x - μ • x),
      mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [hcoeff, mul_pow]
    have hsq : δ ^ 2 ≤ (hA.eigenvalues i - μ) ^ 2 := by
      have h := mul_self_le_mul_self hδ (hn i)
      simpa only [← sq, sq_abs] using h
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  exact (not_lt_of_ge hsum) hres

end GaloisForLFunctions.HTGeometry

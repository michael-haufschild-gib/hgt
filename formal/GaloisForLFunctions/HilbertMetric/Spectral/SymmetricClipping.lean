import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClippingScalar
import GaloisForLFunctions.HilbertMetric.Spectral.ClippedFunctionalCalculus

/-!
# Bounded Hermitian approximations with exact tail error

Clipping both spectral tails produces a matrix between `-c I` and `c I`.
The squared Frobenius error is the sum of squared spectral excesses and
obeys every integral-moment bound. This is the finite-matrix clipping step
of arXiv:2611.18829, equations (3.4)--(3.5).
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.SymmetricClipping
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Symmetric spectral truncation of a Hermitian matrix. -/
def matrix {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) : Matrix ι ι ℂ :=
  specMap hA (clip c)

theorem matrix_hermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    (matrix hA c).IsHermitian := specMap_isHermitian hA _

/-- Both sides of the spectral cap hold, including for indefinite input. -/
theorem matrix_bounds {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    (((c : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - matrix hA c).PosSemidef ∧
      (matrix hA c - ((-(c : ℝ)) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
  constructor
  · rw [matrix, ← Clipped.specMap_constant hA (c : ℝ), ← specMap_sub]
    exact specMap_posSemidef hA fun i => sub_nonneg.mpr (clip_bounds c _).2
  · rw [matrix, ← Complex.ofReal_neg, ← Clipped.specMap_constant hA (-(c : ℝ)),
      ← specMap_sub]
    exact specMap_posSemidef hA fun i => sub_nonneg.mpr (clip_bounds c _).1

theorem error_eq_specMap {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    A - matrix hA c = specMap hA (id - clip c) := by
  rw [specMap_sub, specMap_id, matrix]

/-- Clipping does not mix the original eigenspaces. -/
theorem matrix_commutes {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    A * matrix hA c = matrix hA c * A := by
  conv_lhs => arg 1; rw [← specMap_id hA]
  conv_rhs => arg 2; rw [← specMap_id hA]
  rw [matrix, ← specMap_mul, ← specMap_mul, mul_comm (id : ℝ → ℝ)]

/-- Exact discarded energy, with no normalization or dimension assumption. -/
theorem error_frobSq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    frobSq (A - matrix hA c) =
      ∑ i, max (|hA.eigenvalues i| - c) 0 ^ 2 := by
  rw [error_eq_specMap, frobSq_specMap]
  apply Finset.sum_congr rfl
  intro i _
  exact (sq_abs (hA.eigenvalues i - clip c (hA.eigenvalues i))).symm.trans
    (congrArg (fun t : ℝ => t ^ 2) (abs_sub_clip c _))

/-- Higher moments bound the energy discarded by symmetric clipping. -/
theorem error_moment {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) (n : ℕ) :
    (c : ℝ) ^ n * frobSq (A - matrix hA c) ≤
      Clipped.spectralSum (fun x => |x| ^ (n + 2)) A := by
  rw [error_eq_specMap, frobSq_specMap, Clipped.spectralSum_eq hA, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => clip_error_moment c _ n

/-- The clipped matrix retains no more square energy than the original matrix. -/
theorem matrix_frobSq_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    frobSq (matrix hA c) ≤ frobSq A := by
  rw [matrix, frobSq_specMap, frobSq_hermitian_eq_sum_sq_eigenvalues hA]
  apply Finset.sum_le_sum
  intro i _
  have h := clip_pythagorean c (hA.eigenvalues i)
    (show |(0 : ℝ)| ≤ c by simpa only [abs_zero] using c.coe_nonneg)
  nlinarith only [h, sq_nonneg (hA.eigenvalues i - clip c (hA.eigenvalues i))]

/-- Clipping has zero error precisely when all eigenvalues lie inside the cap. -/
theorem error_eq_zero_iff {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    frobSq (A - matrix hA c) = 0 ↔ ∀ i, |hA.eigenvalues i| ≤ c := by
  rw [error_frobSq, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff,
    max_eq_right_iff, sub_nonpos]

#print axioms matrix_bounds
#print axioms matrix_commutes
#print axioms error_frobSq
#print axioms error_moment
#print axioms matrix_frobSq_le
#print axioms error_eq_zero_iff

end
end GaloisForLFunctions.HilbertMetric.SymmetricClipping

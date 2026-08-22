/-
# The affine-invariant distance in eigenvalue form (Section 5.1.3)

The affine-invariant Riemannian distance on `S⁺⁺(n)` is

```
d_AI(X, Y) = ‖Log(X^{-1/2} Y X^{-1/2})‖_F = ( Σ log² λ_i )^{1/2} ,
```

`λ_i` being the eigenvalues of `X^{-1/2} Y X^{-1/2}`.  This module proves the second equality.

`hermLog` is the spectral logarithm of a symmetric matrix; `exp_hermLog` shows it really is a
logarithm when the eigenvalues are positive, and `frobSq_hermLog` is the eigenvalue formula.
The supporting facts — the squared Frobenius norm as `tr(AᵀA)`, its invariance under orthogonal
congruence, and its value on a diagonal matrix — are mathlib gaps closed here.
-/
import GaloisForLFunctions.HTGeometry.ConstitutivePositiveConeMidpointRecovery

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Matrix
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Frobenius norm of a real matrix. -/
def frobSq (A : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

omit [DecidableEq n] in
theorem frobSq_eq_trace (A : Matrix n n ℝ) : frobSq A = Matrix.trace (Aᵀ * A) := by
  simp only [frobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem frobSq_conj (U A : Matrix n n ℝ) (hU : Uᵀ * U = 1) :
    frobSq (U * A * Uᵀ) = frobSq A := by
  rw [frobSq_eq_trace, frobSq_eq_trace]
  have h1 : (U * A * Uᵀ)ᵀ * (U * A * Uᵀ) = U * (Aᵀ * A) * Uᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Uᵀᵀ * (Aᵀ * Uᵀ) * (U * A * Uᵀ)
        = U * Aᵀ * (Uᵀ * U) * A * Uᵀ := by
          rw [Matrix.transpose_transpose]; simp only [Matrix.mul_assoc]
      _ = U * (Aᵀ * A) * Uᵀ := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem frobSq_diagonal (v : n → ℝ) : frobSq (Matrix.diagonal v) = ∑ i, v i ^ 2 := by
  simp only [frobSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), pow_two, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The spectral logarithm of a real symmetric matrix. -/
noncomputable def hermLog {M : Matrix n n ℝ} (hM : M.IsHermitian) : Matrix n n ℝ :=
  (hM.eigenvectorUnitary : Matrix n n ℝ)
    * Matrix.diagonal (fun i => Real.log (hM.eigenvalues i))
    * (hM.eigenvectorUnitary : Matrix n n ℝ)ᵀ

/-- **Section 5.1.3.**  The squared Frobenius norm of the spectral logarithm is the sum of the
squared logarithms of the eigenvalues. -/
theorem frobSq_hermLog {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    frobSq (hermLog hM) = ∑ i, Real.log (hM.eigenvalues i) ^ 2 := by
  have hU : ((hM.eigenvectorUnitary : Matrix n n ℝ))ᵀ * (hM.eigenvectorUnitary : Matrix n n ℝ)
      = 1 := by
    have h := Matrix.UnitaryGroup.star_mul_self hM.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [hermLog, frobSq_conj _ _ hU, frobSq_diagonal]

/-- `hermLog` is a genuine matrix logarithm: for a symmetric matrix with positive eigenvalues
(i.e. a symmetric positive definite matrix) its matrix exponential is the matrix itself. -/
theorem exp_hermLog {M : Matrix n n ℝ} (hM : M.IsHermitian) (hpos : ∀ i, 0 < hM.eigenvalues i) :
    NormedSpace.exp (hermLog hM) = M := by
  set U : Matrix n n ℝ := (hM.eigenvectorUnitary : Matrix n n ℝ) with hUdef
  have hstar : star U = Uᵀ := by
    rw [hUdef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hUT : Uᵀ * U = 1 := by
    have h := Matrix.UnitaryGroup.star_mul_self hM.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hUT2 : U * Uᵀ = 1 := mul_eq_one_comm.mpr hUT
  have hUinv : U⁻¹ = Uᵀ := Matrix.inv_eq_right_inv hUT2
  have hUunit : IsUnit U := ⟨⟨U, Uᵀ, hUT2, hUT⟩, rfl⟩
  have hexp : NormedSpace.exp (U * Matrix.diagonal (fun i => Real.log (hM.eigenvalues i)) * Uᵀ)
      = U * NormedSpace.exp (Matrix.diagonal (fun i => Real.log (hM.eigenvalues i))) * Uᵀ := by
    rw [← hUinv, Matrix.exp_conj U _ hUunit, hUinv]
  have hpi : (NormedSpace.exp (fun i => Real.log (hM.eigenvalues i)) : n → ℝ)
      = fun i => hM.eigenvalues i := by
    rw [Pi.exp_def]
    funext i
    rw [← congrFun Real.exp_eq_exp_ℝ (Real.log (hM.eigenvalues i)), Real.exp_log (hpos i)]
  have hdiag : NormedSpace.exp (Matrix.diagonal (fun i => Real.log (hM.eigenvalues i)))
      = Matrix.diagonal (fun i => hM.eigenvalues i) := by
    rw [Matrix.exp_diagonal, hpi]
  rw [hermLog, hexp, hdiag]
  conv_rhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [hstar]
  have hdiag2 : (Matrix.diagonal fun i => hM.eigenvalues i)
      = Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) := by
    congr 1
  rw [hdiag2, hUdef]

end GaloisForLFunctions.HTGeometry.HadamardLipschitz

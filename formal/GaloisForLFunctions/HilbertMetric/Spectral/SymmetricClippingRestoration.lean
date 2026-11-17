import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClipping
import GaloisForLFunctions.HTGeometry.HermitianInertia
import Mathlib.Analysis.Real.Sqrt

/-!
# Exact witness transport through symmetric clipping

Positive spectral rescaling restores the original Hermitian form from its
clipped matrix. The reciprocal factors also identify the actual kernels.
Thus clipping transports every signed quadratic witness explicitly.
-/

open Matrix RiemannGaussian.HermitianRankTrace
namespace GaloisForLFunctions.HilbertMetric.SymmetricClipping
noncomputable section
open scoped NNReal

/-- Coefficient amplification that restores a clipped spectral component. -/
def restoreFactor (c : ℝ≥0) (x : ℝ) : ℝ := Real.sqrt (max 1 (|x| / (c : ℝ)))

theorem restoreFactor_pos (c : ℝ≥0) (x : ℝ) : 0 < restoreFactor c x :=
  Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

theorem restoreFactor_sq (c : ℝ≥0) (x : ℝ) :
    restoreFactor c x ^ 2 = max 1 (|x| / (c : ℝ)) :=
  Real.sq_sqrt (le_trans zero_le_one (le_max_left _ _))

/-- Exact scalar congruence, including the zero eigenvalue. -/
theorem restoreFactor_clip (c : ℝ≥0) (hc : 0 < c) (x : ℝ) :
    restoreFactor c x * clip c x * restoreFactor c x = x := by
  have hc' : (0 : ℝ) < c := hc
  by_cases h : |x| ≤ c
  · have hd : |x| / (c : ℝ) ≤ 1 := (div_le_one₀ hc').mpr h
    rw [restoreFactor, max_eq_left hd, Real.sqrt_one, one_mul, mul_one, clip_of_abs_le c h]
  · have hgt : (c : ℝ) < |x| := lt_of_not_ge h
    have hd : 1 ≤ |x| / (c : ℝ) :=
      (le_div_iff₀ hc').mpr (by simpa only [one_mul] using hgt.le)
    have hs : restoreFactor c x ^ 2 * (c : ℝ) = |x| := by
      have hsq := restoreFactor_sq c x
      rw [max_eq_right hd] at hsq
      exact ((div_eq_iff hc'.ne').mp hsq.symm).symm
    by_cases hx : x ≤ 0
    · rw [abs_of_nonpos hx] at hs hgt
      rw [clip_of_le_neg c (by linarith only [hgt])]
      nlinarith only [hs]
    · have hx' : 0 ≤ x := (lt_of_not_ge hx).le
      rw [abs_of_nonneg hx'] at hs hgt
      rw [clip_of_ge c hgt.le]
      nlinarith only [hs]

private theorem inverse_restoreFactor (c : ℝ≥0) (hc : 0 < c) (x : ℝ) :
    (restoreFactor c x)⁻¹ * (restoreFactor c x)⁻¹ * x = clip c x := by
  calc
    _ = (restoreFactor c x)⁻¹ * (restoreFactor c x)⁻¹ *
        (restoreFactor c x * clip c x * restoreFactor c x) :=
      congrArg (fun z => (restoreFactor c x)⁻¹ * (restoreFactor c x)⁻¹ * z)
        (restoreFactor_clip c hc x).symm
    _ = ((restoreFactor c x)⁻¹ * restoreFactor c x) *
        ((restoreFactor c x)⁻¹ * restoreFactor c x) * clip c x := by ring
    _ = _ := by rw [inv_mul_cancel₀ (restoreFactor_pos c x).ne']; simp only [one_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spectral change of coefficients restoring the original quadratic form. -/
def restoreMatrix {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) : Matrix ι ι ℂ :=
  specMap hA (restoreFactor c)

/-- Its reciprocal spectral change of coefficients. -/
def inverseRestoreMatrix {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) : Matrix ι ι ℂ :=
  specMap hA ((restoreFactor c)⁻¹)

theorem restoreMatrix_hermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    (restoreMatrix hA c).IsHermitian := specMap_isHermitian hA _

/-- Both coefficient changes are inverse matrices, including on null modes. -/
theorem restoreMatrix_inverse {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    restoreMatrix hA c * inverseRestoreMatrix hA c = 1 ∧
      inverseRestoreMatrix hA c * restoreMatrix hA c = 1 := by
  have hf : restoreFactor c * (restoreFactor c)⁻¹ = (fun _ : ℝ => 1) := by
    funext x
    exact mul_inv_cancel₀ (restoreFactor_pos c x).ne'
  have hg : (restoreFactor c)⁻¹ * restoreFactor c = (fun _ : ℝ => 1) := by
    funext x
    exact inv_mul_cancel₀ (restoreFactor_pos c x).ne'
  constructor
  · rw [restoreMatrix, inverseRestoreMatrix, ← specMap_mul, hf, Clipped.specMap_constant]
    simp only [Complex.ofReal_one, one_smul]
  · rw [restoreMatrix, inverseRestoreMatrix, ← specMap_mul, hg, Clipped.specMap_constant]
    simp only [Complex.ofReal_one, one_smul]

/-- Clipping is an exact invertible congruence of the original Hermitian form. -/
theorem restoreMatrix_congruence {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (c : ℝ≥0) (hc : 0 < c) :
    (restoreMatrix hA c)ᴴ * matrix hA c * restoreMatrix hA c = A := by
  have hf : (restoreFactor c * clip c) * restoreFactor c = id := by
    funext x
    exact restoreFactor_clip c hc x
  rw [(restoreMatrix_hermitian hA c).eq, restoreMatrix, matrix,
    ← specMap_mul, ← specMap_mul, hf, specMap_id]

private theorem restoration_factorizations {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (c : ℝ≥0) (hc : 0 < c) :
    A = (restoreMatrix hA c * restoreMatrix hA c) * matrix hA c ∧
      matrix hA c = (inverseRestoreMatrix hA c * inverseRestoreMatrix hA c) * A := by
  have hf : (restoreFactor c * restoreFactor c) * clip c = id := by
    funext x
    change restoreFactor c x * restoreFactor c x * clip c x = x
    calc
      _ = restoreFactor c x * clip c x * restoreFactor c x := by ring
      _ = x := restoreFactor_clip c hc x
  have hg : ((restoreFactor c)⁻¹ * (restoreFactor c)⁻¹) * id = clip c := by
    funext x
    exact inverse_restoreFactor c hc x
  constructor
  · rw [restoreMatrix, matrix, ← specMap_mul, ← specMap_mul, hf, specMap_id]
  · calc
      _ = specMap hA (((restoreFactor c)⁻¹ * (restoreFactor c)⁻¹) * id) :=
        congrArg (specMap hA) hg.symm
      _ = _ := by rw [specMap_mul, specMap_mul, specMap_id]; rfl

/-- The entire kernel subspace is unchanged by a positive cutoff. -/
theorem matrix_kernel {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (c : ℝ≥0) (hc : 0 < c) :
    LinearMap.ker (matrix hA c).mulVecLin = LinearMap.ker A.mulVecLin := by
  have hf := restoration_factorizations hA c hc
  ext v
  change matrix hA c *ᵥ v = 0 ↔ A *ᵥ v = 0
  constructor
  · intro hv
    rw [hf.1, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · intro hv
    rw [hf.2, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- Every original quadratic value is attained by the explicit transformed coefficients. -/
theorem matrix_quadratic_transport {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (c : ℝ≥0) (hc : 0 < c) (v : ι → ℂ) :
    HTGeometry.hermQuad (matrix hA c) (restoreMatrix hA c *ᵥ v) = HTGeometry.hermQuad A v := by
  rw [← HTGeometry.hermQuad_conjugate, restoreMatrix_congruence hA c hc]

#print axioms restoreMatrix_inverse
#print axioms restoreMatrix_congruence
#print axioms matrix_kernel
#print axioms matrix_quadratic_transport

end
end GaloisForLFunctions.HilbertMetric.SymmetricClipping


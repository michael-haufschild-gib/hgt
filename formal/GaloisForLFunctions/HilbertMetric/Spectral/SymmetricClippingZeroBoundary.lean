import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClippingRestoration

/-!
# The exact zero boundary of symmetric clipping

The reciprocal restoration matrix transports the clipped form back to the
original one. A clipped matrix vanishes exactly when its cap or its input
vanishes. Indefiniteness survives exactly at nonzero caps, with explicit
coefficient transports in both directions.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped NNReal
noncomputable section
namespace GaloisForLFunctions.HilbertMetric.SymmetricClipping
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A zero spectral cap annihilates every Hermitian matrix. -/
theorem matrix_cutoff_zero {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : matrix hA 0 = 0 := by
  have hc : clip 0 = (fun _ : ℝ => 0) := by
    funext x
    exact le_antisymm (by simpa only [NNReal.coe_zero] using (clip_bounds 0 x).2)
      (by simpa only [NNReal.coe_zero, neg_zero] using (clip_bounds 0 x).1)
  rw [matrix, hc, Clipped.specMap_constant]
  simp only [Complex.ofReal_zero, zero_smul]

/-- The reciprocal change of coefficients recovers the clipped form from the original one. -/
theorem inverseRestoreMatrix_congruence {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (c : ℝ≥0) (hc : 0 < c) :
    (inverseRestoreMatrix hA c)ᴴ * A * inverseRestoreMatrix hA c = matrix hA c := by
  have hU : (inverseRestoreMatrix hA c).IsHermitian := specMap_isHermitian hA _
  have h := restoreMatrix_congruence hA c hc
  rw [(restoreMatrix_hermitian hA c).eq] at h
  have hu := restoreMatrix_inverse hA c
  rw [hU.eq]
  calc
    _ = inverseRestoreMatrix hA c * (restoreMatrix hA c * matrix hA c * restoreMatrix hA c) *
        inverseRestoreMatrix hA c :=
      congrArg (fun B => inverseRestoreMatrix hA c * B * inverseRestoreMatrix hA c) h.symm
    _ = (inverseRestoreMatrix hA c * restoreMatrix hA c) * matrix hA c *
        (restoreMatrix hA c * inverseRestoreMatrix hA c) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu.1, hu.2, Matrix.one_mul, Matrix.mul_one]

/-- Complete annihilation occurs exactly at a zero cap or for a zero input matrix. -/
theorem matrix_eq_zero_iff {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    matrix hA c = 0 ↔ c = 0 ∨ A = 0 := by
  constructor
  · intro hz
    by_cases hc : c = 0
    · exact Or.inl hc
    · have hcpos : 0 < c := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ c) (Ne.symm hc)
      have h := restoreMatrix_congruence hA c hcpos
      rw [hz, Matrix.mul_zero, Matrix.zero_mul] at h
      exact Or.inr h.symm
  · rintro (rfl | hzero)
    · exact matrix_cutoff_zero hA
    · by_cases hc : c = 0
      · subst c
        exact matrix_cutoff_zero hA
      · have hcpos : 0 < c := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ c) (Ne.symm hc)
        have h := inverseRestoreMatrix_congruence hA c hcpos
        apply h.symm.trans
        calc
          _ = (inverseRestoreMatrix hA c)ᴴ * 0 * inverseRestoreMatrix hA c :=
            congrArg (fun B => (inverseRestoreMatrix hA c)ᴴ * B * inverseRestoreMatrix hA c) hzero
          _ = 0 := by rw [Matrix.mul_zero, Matrix.zero_mul]

/-- The inverse coefficient change transports every clipped quadratic value back to the original form. -/
theorem inverse_matrix_quadratic_transport {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (c : ℝ≥0) (hc : 0 < c) (v : ι → ℂ) :
    HTGeometry.hermQuad A (inverseRestoreMatrix hA c *ᵥ v) =
      HTGeometry.hermQuad (matrix hA c) v := by
  rw [← HTGeometry.hermQuad_conjugate, inverseRestoreMatrix_congruence hA c hc]

/-- A clipped Hermitian form is indefinite exactly when the cap is positive and the original form is indefinite. -/
theorem matrix_both_signs_iff {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    (∃ v w : ι → ℂ, HTGeometry.hermQuad (matrix hA c) v < 0 ∧
      0 < HTGeometry.hermQuad (matrix hA c) w) ↔
    c ≠ 0 ∧ ∃ v w : ι → ℂ, HTGeometry.hermQuad A v < 0 ∧ 0 < HTGeometry.hermQuad A w := by
  constructor
  · rintro ⟨v, w, hv, hw⟩
    have hc : c ≠ 0 := by
      intro hz
      subst c
      rw [matrix_cutoff_zero hA] at hv
      simp only [HTGeometry.hermQuad, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re,
        lt_self_iff_false] at hv
    have hcpos : 0 < c := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ c) (Ne.symm hc)
    refine ⟨hc, inverseRestoreMatrix hA c *ᵥ v, inverseRestoreMatrix hA c *ᵥ w, ?_, ?_⟩
    · rw [inverse_matrix_quadratic_transport hA c hcpos]
      exact hv
    · rw [inverse_matrix_quadratic_transport hA c hcpos]
      exact hw
  · rintro ⟨hc, v, w, hv, hw⟩
    have hcpos : 0 < c := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ c) (Ne.symm hc)
    refine ⟨restoreMatrix hA c *ᵥ v, restoreMatrix hA c *ᵥ w, ?_, ?_⟩
    · rw [matrix_quadratic_transport hA c hcpos]
      exact hv
    · rw [matrix_quadratic_transport hA c hcpos]
      exact hw

#print axioms matrix_both_signs_iff

#print axioms inverseRestoreMatrix_congruence
#print axioms matrix_eq_zero_iff
end GaloisForLFunctions.HilbertMetric.SymmetricClipping

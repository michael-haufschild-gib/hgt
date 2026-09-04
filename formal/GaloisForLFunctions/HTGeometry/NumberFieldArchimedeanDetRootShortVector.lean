import GaloisForLFunctions.HTGeometry.NumberFieldIntegerVectorDetRootMinimum
import GaloisForLFunctions.HTGeometry.PositiveDefiniteCoordinateFrame
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanPrimitiveMinimum

/-!
# Determinant-root short vectors for corrected archimedean forms

The canonical real matrix of a corrected real/Hermitian form is factored by its positive Jacobi
frame.  Determinant-normalized Minkowski reduction then gives a literal nonzero number-ring vector,
whose exact archimedean energy is bounded by the determinant root of that frame.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField Module
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Canonical Jacobi square-root data for the real matrix of a corrected archimedean form. -/
def numberFieldArchimedeanCanonicalJacobiData
    (A : numberFieldArchimedeanPositiveForms K n) :
    JacobiData (n * Module.finrank ℚ K) :=
  Classical.choose (exists_jacobiData
    (numberFieldArchimedeanCanonicalMatrix_posDef A))

/-- The chosen Jacobi frame represents the canonical real matrix exactly. -/
theorem numberFieldArchimedeanCanonicalJacobiData_form
    (A : numberFieldArchimedeanPositiveForms K n) :
    (numberFieldArchimedeanCanonicalJacobiData A).form =
      numberFieldArchimedeanCanonicalMatrix A :=
  Classical.choose_spec (exists_jacobiData
    (numberFieldArchimedeanCanonicalMatrix_posDef A))

/-- The squared canonical-frame determinant is the determinant of the canonical real form. -/
theorem numberFieldArchimedeanCanonicalFrame_det_sq
    (A : numberFieldArchimedeanPositiveForms K n) :
    (numberFieldArchimedeanCanonicalJacobiData A).frameMatrix.det ^ 2 =
      (numberFieldArchimedeanCanonicalMatrix A).det := by
  rw [(numberFieldArchimedeanCanonicalJacobiData A).frameMatrix_det_sq,
    numberFieldArchimedeanCanonicalJacobiData_form]

/-- Uniform Hermite--Minkowski bound for a nonzero number-ring vector in every corrected
archimedean form, expressed directly through the determinant root of its canonical real matrix. -/
theorem exists_uniform_numberFieldArchimedeanEnergy_le_canonicalDetRoot
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 0 < n) :
    ∃ R : ℝ, 0 < R ∧
      ∀ A : numberFieldArchimedeanPositiveForms K n,
        ∃ a : Fin n → RingOfIntegers K, a ≠ 0 ∧
          numberFieldArchimedeanEnergy A
              (numberFieldIntegerVectorEmbedding K a) ≤
            ((n * Module.finrank ℚ K : ℕ) : ℝ) *
              R ^ 2 * Real.rpow (numberFieldArchimedeanCanonicalMatrix A).det
                (((n * Module.finrank ℚ K : ℕ) : ℝ)⁻¹) := by
  obtain ⟨R, hR, hbound⟩ :=
    exists_uniform_numberFieldIntegerVectorEmbedding_linearEquiv_norm_le_detRoot
      K n hn
  refine ⟨R, hR, ?_⟩
  intro A
  let J := numberFieldArchimedeanCanonicalJacobiData A
  let T := J.frameCoordinateContinuousLinearEquiv
  obtain ⟨a, ha0, ha⟩ := hbound T
  refine ⟨a, ha0, ?_⟩
  let c := numberFieldMixedVectorContinuousLinearEquiv K n
    (numberFieldIntegerVectorEmbedding K a)
  have henergy : numberFieldArchimedeanEnergy A
      (numberFieldIntegerVectorEmbedding K a) = ∑ i, (T c i) ^ 2 := by
    calc
      numberFieldArchimedeanEnergy A (numberFieldIntegerVectorEmbedding K a) =
          c ⬝ᵥ (numberFieldArchimedeanCanonicalMatrix A).mulVec c :=
        (numberFieldArchimedeanCanonicalMatrix_quadratic A
          (numberFieldIntegerVectorEmbedding K a)).symm
      _ = c ⬝ᵥ J.form.mulVec c := by
        rw [numberFieldArchimedeanCanonicalJacobiData_form]
      _ = ∑ i, (T c i) ^ 2 := by
        exact (J.sum_sq_frameCoordinateContinuousLinearEquiv c).symm
  have hsum : ∑ i, (T c i) ^ 2 ≤
      ((n * Module.finrank ℚ K : ℕ) : ℝ) * ‖T c‖ ^ 2 :=
    sum_sq_le_card_mul_pi_norm_sq (T c)
  have hdet : LinearMap.det
      (T : (Fin (n * Module.finrank ℚ K) → ℝ) →ₗ[ℝ]
        (Fin (n * Module.finrank ℚ K) → ℝ)) = J.frameMatrix.det :=
    J.det_frameCoordinateContinuousLinearEquiv
  have ha' : ‖T c‖ ≤ R * Real.rpow |J.frameMatrix.det|
      (((n * Module.finrank ℚ K : ℕ) : ℝ)⁻¹) := by
    simpa [T, c, hdet] using ha
  have hnonneg : 0 ≤ R * Real.rpow |J.frameMatrix.det|
      (((n * Module.finrank ℚ K : ℕ) : ℝ)⁻¹) :=
    mul_nonneg hR.le (Real.rpow_nonneg (abs_nonneg _) _)
  rw [henergy]
  calc
    ∑ i, (T c i) ^ 2 ≤
        ((n * Module.finrank ℚ K : ℕ) : ℝ) * ‖T c‖ ^ 2 := hsum
    _ ≤ ((n * Module.finrank ℚ K : ℕ) : ℝ) *
        (R * Real.rpow |J.frameMatrix.det|
          (((n * Module.finrank ℚ K : ℕ) : ℝ)⁻¹)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _
        (Nat.cast_nonneg (n * Module.finrank ℚ K))
      nlinarith [norm_nonneg (T c)]
    _ = ((n * Module.finrank ℚ K : ℕ) : ℝ) * R ^ 2 *
        Real.rpow (numberFieldArchimedeanCanonicalMatrix A).det
          (((n * Module.finrank ℚ K : ℕ) : ℝ)⁻¹) := by
      rw [mul_pow, J.rpow_abs_frameMatrix_det_sq,
        numberFieldArchimedeanCanonicalJacobiData_form]
      ring

end

end GaloisForLFunctions.HTGeometry

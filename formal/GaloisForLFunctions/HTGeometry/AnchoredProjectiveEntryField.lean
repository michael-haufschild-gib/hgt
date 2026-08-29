import GaloisForLFunctions.HTGeometry.CorcoranDeLeeuwModelOne
import GaloisForLFunctions.HTGeometry.ProjectiveWignerSmithDifferentialField
import GaloisForLFunctions.HTGeometry.SingleGeneratorDifferentialDegree

/-!
# The anchored projective field of the model-1 family

Anchoring the second spectral parameter at a fixed point turns the model-1 matrix into a matrix
over a differential field whose entries are the base scalars together with a single increment `h`.
Its pivot-normalised entry family therefore generates exactly the differential field `F⟨h⟩`, and
that field has differential transcendence degree one precisely when `h` is hypertranscendental
over `F`.  Scalar normalisation cannot remove it: the pivot-normalised family is invariant under
rescaling the whole matrix.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

universe u

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Differential F] [Differential E] [DifferentialAlgebra F E]

/-- Pivot-normalised entry family of a matrix over an arbitrary finite index type. -/
def pivotEntryFamily {ι : Type*} (S : Matrix ι ι E) (p : ι × ι) : ι × ι → E :=
  fun r => (S p.1 p.2)⁻¹ * S r.1 r.2

omit [Differential E] in
theorem pivotEntryFamily_eq_matrixPivotNormalize {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (p r : Fin (n + 1) × Fin (n + 1)) :
    pivotEntryFamily S p r = matrixPivotNormalize S p r.1 r.2 := rfl

omit [Differential E] in
/-- Rescaling the whole matrix leaves the pivot-normalised entry family unchanged. -/
theorem pivotEntryFamily_smul {ι : Type*} (S : Matrix ι ι E) (p : ι × ι)
    (c : E) (hc : c ≠ 0) (hp : S p.1 p.2 ≠ 0) :
    pivotEntryFamily (c • S) p = pivotEntryFamily S p := by
  funext r
  simp only [pivotEntryFamily, Matrix.smul_apply, smul_eq_mul, mul_inv]
  field_simp

/-- A family all of whose members lie in `F⟨h⟩` and which attains `h` generates exactly `F⟨h⟩`. -/
theorem differentialAdjoin_range_eq_singleton
    {ι : Type*} (y : ι → E) (i₀ : ι) (h : E)
    (hy : ∀ i, y i ∈ differentialAdjoin F ({h} : Set E)) (hi₀ : y i₀ = h) :
    differentialAdjoin F (Set.range y) = differentialAdjoin F ({h} : Set E) := by
  apply le_antisymm
  · exact differentialAdjoin_le F (by rintro _ ⟨i, rfl⟩; exact hy i)
      (derivationClosed_differentialAdjoin F _)
  · refine differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _)
    rintro _ rfl
    exact hi₀ ▸ subset_differentialAdjoin F (Set.range y) ⟨i₀, rfl⟩

/-- **The anchored projective field of the model-1 matrix is `F⟨h⟩`.**  With the second clock
anchored at a base point, all entries of the regular matrix lie in the base field except the single
increment `h` of the free analytic clock, and the pivot entry is the constant `1`. -/
theorem differentialAdjoin_pivotEntryFamily_modelOneR (g₀ : F) (h : E) :
    differentialAdjoin F
        (Set.range (pivotEntryFamily (modelOneR (0 : E) h (algebraMap F E g₀))
          ((0, 0), (0, 0)))) =
      differentialAdjoin F ({h} : Set E) := by
  refine differentialAdjoin_range_eq_singleton _ ((0, 0), (1, 0)) h ?_ ?_
  · rintro ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp only [pivotEntryFamily, modelOneR, Matrix.of_apply]
    all_goals norm_num
    all_goals
      first
        | exact IntermediateField.one_mem _
        | exact IntermediateField.zero_mem _
        | exact IntermediateField.algebraMap_mem _ g₀
        | exact subset_differentialAdjoin F ({h} : Set E) rfl
  · simp [pivotEntryFamily, modelOneR]

/-- **Anchored projective differential transcendence degree one.**  The anchored projective field
of the model-1 matrix is exactly `F⟨h⟩`, and when the free clock increment `h` is
hypertranscendental over the base that field is a one-dimensional differential extension. -/
theorem anchoredModelOne_projectiveField_degree [CharZero E]
    (g₀ : F) {h : E} (hh : HypertranscendentalOver F h) :
    differentialAdjoin F
        (Set.range (pivotEntryFamily (modelOneR (0 : E) h (algebraMap F E g₀))
          ((0, 0), (0, 0)))) = differentialAdjoin F ({h} : Set E) ∧
      (letI := derivationClosedDifferential (differentialAdjoin F ({h} : Set E))
        (derivationClosed_differentialAdjoin F ({h} : Set E))
       differentialTranscendenceDegree F (differentialAdjoin F ({h} : Set E)) = 1) :=
  ⟨differentialAdjoin_pivotEntryFamily_modelOneR g₀ h,
    differentialTranscendenceDegree_differentialAdjoin_singleton_eq_one hh⟩

end

end GaloisForLFunctions.HTGeometry

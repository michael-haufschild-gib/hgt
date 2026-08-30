import GaloisForLFunctions.HTGeometry.NumberFieldMixedVectorPlaceCoordinates
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The archimedean positive cone of a number field

The symmetric space for a number field is placewise: real places carry real symmetric forms and
complex places carry complex Hermitian forms.  This distinction is essential; requiring every
number-field scalar to be self-adjoint in one real regular representation would make the positive
cone empty as soon as a complex place is present.

This file builds the correct nonempty cone and the exact congruence action of
`SL_n(𝓞 K)`.  Evaluation, determinant one, invertibility, Hermiticity, positivity, and the action
laws are all discharged internally.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Real-symmetric and complex-Hermitian matrices at every infinite place. -/
abbrev numberFieldArchimedeanForms (K : Type*) [Field K] (n : ℕ) :=
  ({w : InfinitePlace K // w.IsReal} → selfAdjoint (Matrix (Fin n) (Fin n) ℝ)) ×
    ({w : InfinitePlace K // w.IsComplex} → selfAdjoint (Matrix (Fin n) (Fin n) ℂ))

/-- Positive-definite placewise real/Hermitian forms. -/
def numberFieldArchimedeanCone (K : Type*) [Field K] (n : ℕ) :
    Set (numberFieldArchimedeanForms K n) :=
  {A | (∀ w, ((A.1 w : selfAdjoint (Matrix (Fin n) (Fin n) ℝ)) :
      Matrix (Fin n) (Fin n) ℝ).PosDef) ∧
    ∀ w, ((A.2 w : selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ).PosDef}

/-- Evaluate a number-ring matrix at a real infinite place. -/
def numberFieldRealOrderMatrixAt (w : {w : InfinitePlace K // w.IsReal})
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) : Matrix (Fin n) (Fin n) ℝ :=
  ((w.1.embedding_of_isReal w.2).comp (algebraMap (𝓞 K) K)).mapMatrix M

/-- Evaluate a number-ring matrix at a chosen complex embedding of a complex infinite place. -/
def numberFieldComplexOrderMatrixAt (w : {w : InfinitePlace K // w.IsComplex})
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) : Matrix (Fin n) (Fin n) ℂ :=
  (w.1.embedding.comp (algebraMap (𝓞 K) K)).mapMatrix M

omit [NumberField K] in
@[simp]
theorem numberFieldRealOrderMatrixAt_one
    (w : {w : InfinitePlace K // w.IsReal}) :
    numberFieldRealOrderMatrixAt w (1 : Matrix (Fin n) (Fin n) (𝓞 K)) = 1 := by
  exact map_one _

omit [NumberField K] in
@[simp]
theorem numberFieldComplexOrderMatrixAt_one
    (w : {w : InfinitePlace K // w.IsComplex}) :
    numberFieldComplexOrderMatrixAt w (1 : Matrix (Fin n) (Fin n) (𝓞 K)) = 1 := by
  exact map_one _

omit [NumberField K] in
@[simp]
theorem numberFieldRealOrderMatrixAt_mul
    (w : {w : InfinitePlace K // w.IsReal})
    (M N : Matrix (Fin n) (Fin n) (𝓞 K)) :
    numberFieldRealOrderMatrixAt w (M * N) =
      numberFieldRealOrderMatrixAt w M * numberFieldRealOrderMatrixAt w N := by
  exact map_mul _ _ _

omit [NumberField K] in
@[simp]
theorem numberFieldComplexOrderMatrixAt_mul
    (w : {w : InfinitePlace K // w.IsComplex})
    (M N : Matrix (Fin n) (Fin n) (𝓞 K)) :
    numberFieldComplexOrderMatrixAt w (M * N) =
      numberFieldComplexOrderMatrixAt w M * numberFieldComplexOrderMatrixAt w N := by
  exact map_mul _ _ _

omit [NumberField K] in
theorem numberFieldRealOrderMatrixAt_det
    (w : {w : InfinitePlace K // w.IsReal})
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) :
    (numberFieldRealOrderMatrixAt w M).det =
      (w.1.embedding_of_isReal w.2).comp (algebraMap (𝓞 K) K) M.det := by
  exact (RingHom.map_det _ _).symm

omit [NumberField K] in
theorem numberFieldComplexOrderMatrixAt_det
    (w : {w : InfinitePlace K // w.IsComplex})
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) :
    (numberFieldComplexOrderMatrixAt w M).det =
      w.1.embedding.comp (algebraMap (𝓞 K) K) M.det := by
  exact (RingHom.map_det _ _).symm

omit [NumberField K] in
@[simp]
theorem numberFieldRealSpecialLinearAt_det
    (w : {w : InfinitePlace K // w.IsReal})
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
    (numberFieldRealOrderMatrixAt w (g : Matrix (Fin n) (Fin n) (𝓞 K))).det = 1 := by
  rw [numberFieldRealOrderMatrixAt_det, Matrix.SpecialLinearGroup.det_coe, map_one]

omit [NumberField K] in
@[simp]
theorem numberFieldComplexSpecialLinearAt_det
    (w : {w : InfinitePlace K // w.IsComplex})
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
    (numberFieldComplexOrderMatrixAt w (g : Matrix (Fin n) (Fin n) (𝓞 K))).det = 1 := by
  rw [numberFieldComplexOrderMatrixAt_det, Matrix.SpecialLinearGroup.det_coe, map_one]

omit [NumberField K] in
theorem numberFieldRealSpecialLinearAt_isUnit
    (w : {w : InfinitePlace K // w.IsReal})
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
    IsUnit (numberFieldRealOrderMatrixAt w (g : Matrix (Fin n) (Fin n) (𝓞 K))) := by
  rw [Matrix.isUnit_iff_isUnit_det, numberFieldRealSpecialLinearAt_det]
  exact isUnit_one

omit [NumberField K] in
theorem numberFieldComplexSpecialLinearAt_isUnit
    (w : {w : InfinitePlace K // w.IsComplex})
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
    IsUnit (numberFieldComplexOrderMatrixAt w (g : Matrix (Fin n) (Fin n) (𝓞 K))) := by
  rw [Matrix.isUnit_iff_isUnit_det, numberFieldComplexSpecialLinearAt_det]
  exact isUnit_one

/-- Placewise congruence by an integral special-linear matrix. -/
def numberFieldArchimedeanConj
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (A : numberFieldArchimedeanForms K n) : numberFieldArchimedeanForms K n :=
  (fun w =>
    let G := numberFieldRealOrderMatrixAt w (g : Matrix (Fin n) (Fin n) (𝓞 K))
    ⟨G * (A.1 w : Matrix (Fin n) (Fin n) ℝ) * Gᴴ, by
      change (G * (A.1 w : Matrix (Fin n) (Fin n) ℝ) * Gᴴ)ᴴ = _
      have hA : ((A.1 w : Matrix (Fin n) (Fin n) ℝ))ᴴ = A.1 w := (A.1 w).prop
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA]
      simp only [Matrix.mul_assoc]⟩,
   fun w =>
    let G := numberFieldComplexOrderMatrixAt w (g : Matrix (Fin n) (Fin n) (𝓞 K))
    ⟨G * (A.2 w : Matrix (Fin n) (Fin n) ℂ) * Gᴴ, by
      change (G * (A.2 w : Matrix (Fin n) (Fin n) ℂ) * Gᴴ)ᴴ = _
      have hA : ((A.2 w : Matrix (Fin n) (Fin n) ℂ))ᴴ = A.2 w := (A.2 w).prop
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA]
      simp only [Matrix.mul_assoc]⟩)

omit [NumberField K] in
theorem numberFieldArchimedeanConj_one (A : numberFieldArchimedeanForms K n) :
    numberFieldArchimedeanConj (1 : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) A = A := by
  apply Prod.ext <;> funext w <;> apply Subtype.ext
  · simp [numberFieldArchimedeanConj]
  · simp [numberFieldArchimedeanConj]

omit [NumberField K] in
theorem numberFieldArchimedeanConj_mul
    (g h : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (A : numberFieldArchimedeanForms K n) :
    numberFieldArchimedeanConj (g * h) A =
      numberFieldArchimedeanConj g (numberFieldArchimedeanConj h A) := by
  apply Prod.ext <;> funext w <;> apply Subtype.ext
  · simp [numberFieldArchimedeanConj, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simp [numberFieldArchimedeanConj, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]

omit [NumberField K] in
theorem numberFieldArchimedeanConj_mem
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    {A : numberFieldArchimedeanForms K n}
    (hA : A ∈ numberFieldArchimedeanCone K n) :
    numberFieldArchimedeanConj g A ∈ numberFieldArchimedeanCone K n := by
  constructor
  · intro w
    exact (hA.1 w).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit (numberFieldRealSpecialLinearAt_isUnit w g))
  · intro w
    exact (hA.2 w).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit (numberFieldComplexSpecialLinearAt_isUnit w g))

omit [NumberField K] in
/-- The correct archimedean symmetric space is nonempty over every number field. -/
theorem numberFieldArchimedeanCone_nonempty :
    (numberFieldArchimedeanCone K n).Nonempty := by
  let Ireal : {w : InfinitePlace K // w.IsReal} →
      selfAdjoint (Matrix (Fin n) (Fin n) ℝ) :=
    fun _ => ⟨1, Matrix.isHermitian_one⟩
  let Icomplex : {w : InfinitePlace K // w.IsComplex} →
      selfAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
    fun _ => ⟨1, Matrix.isHermitian_one⟩
  refine ⟨(Ireal, Icomplex), ?_, ?_⟩
  · intro w
    exact (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef)
  · intro w
    exact (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℂ).PosDef)

/-- Positive archimedean forms with the induced special-linear action. -/
abbrev numberFieldArchimedeanPositiveForms (K : Type*) [Field K] (n : ℕ) :=
  ↥(numberFieldArchimedeanCone K n)

noncomputable instance numberFieldArchimedeanPositiveFormsMulAction :
    MulAction (Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
      (numberFieldArchimedeanPositiveForms K n) where
  smul g A := ⟨numberFieldArchimedeanConj g A.1,
    numberFieldArchimedeanConj_mem g A.2⟩
  one_smul A := Subtype.ext (numberFieldArchimedeanConj_one A.1)
  mul_smul g h A := Subtype.ext (numberFieldArchimedeanConj_mul g h A.1)

end

end GaloisForLFunctions.HTGeometry

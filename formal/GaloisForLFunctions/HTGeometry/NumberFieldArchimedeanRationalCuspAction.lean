import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanRationalCuspChart

/-!
# Rational special-linear cusp action

The determinant-one number-field congruences form an action on the corrected archimedean cone.
Scalar extension from the number ring restricts this action exactly to the established integral
action, while each rank-two cusp chart is the action of its transposed pseudo-basis frame.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder Matrix NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

omit [NumberField K] in
theorem numberFieldArchimedeanRationalConj_one
    (A : numberFieldArchimedeanForms K n) :
    numberFieldArchimedeanRationalConj
      (1 : Matrix (Fin n) (Fin n) K) A = A := by
  apply Prod.ext <;> funext w <;> apply Subtype.ext
  · simp [numberFieldArchimedeanRationalConj]
  · simp [numberFieldArchimedeanRationalConj]

omit [NumberField K] in
theorem numberFieldArchimedeanRationalConj_mul
    (M N : Matrix (Fin n) (Fin n) K)
    (A : numberFieldArchimedeanForms K n) :
    numberFieldArchimedeanRationalConj (M * N) A =
      numberFieldArchimedeanRationalConj M
        (numberFieldArchimedeanRationalConj N A) := by
  apply Prod.ext <;> funext w <;> apply Subtype.ext
  · simp [numberFieldArchimedeanRationalConj,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simp [numberFieldArchimedeanRationalConj,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Congruence action of rational special-linear matrices on corrected archimedean forms. -/
noncomputable instance numberFieldArchimedeanPositiveFormsRationalMulAction :
    MulAction (Matrix.SpecialLinearGroup (Fin n) K)
      (numberFieldArchimedeanPositiveForms K n) where
  smul g A := numberFieldArchimedeanPositiveRationalConj
    (g : Matrix (Fin n) (Fin n) K) g.2 A
  one_smul A := Subtype.ext (numberFieldArchimedeanRationalConj_one A.1)
  mul_smul g h A := Subtype.ext (numberFieldArchimedeanRationalConj_mul
    (g : Matrix (Fin n) (Fin n) K) (h : Matrix (Fin n) (Fin n) K) A.1)

/-- Entrywise scalar extension of a number-ring matrix to its number field. -/
def numberFieldMatrixBaseChange
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) : Matrix (Fin n) (Fin n) K :=
  (algebraMap (𝓞 K) K).mapMatrix M

omit [NumberField K] in
@[simp]
theorem numberFieldMatrixBaseChange_one :
    numberFieldMatrixBaseChange
      (1 : Matrix (Fin n) (Fin n) (𝓞 K)) = 1 := by
  exact map_one _

omit [NumberField K] in
@[simp]
theorem numberFieldMatrixBaseChange_mul
    (M N : Matrix (Fin n) (Fin n) (𝓞 K)) :
    numberFieldMatrixBaseChange (M * N) =
      numberFieldMatrixBaseChange M * numberFieldMatrixBaseChange N := by
  exact map_mul _ _ _

omit [NumberField K] in
theorem numberFieldMatrixBaseChange_det
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) :
    (numberFieldMatrixBaseChange M).det = algebraMap (𝓞 K) K M.det := by
  exact (RingHom.map_det _ _).symm

/-- Scalar extension embeds the integral special-linear group in the rational one. -/
def numberFieldSpecialLinearBaseChange
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
    Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨numberFieldMatrixBaseChange
      (g : Matrix (Fin n) (Fin n) (𝓞 K)), by
    rw [numberFieldMatrixBaseChange_det, g.2, map_one]⟩

omit [NumberField K] in
@[simp]
theorem numberFieldRealMatrixAt_baseChange
    (w : {w : InfinitePlace K // w.IsReal})
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) :
    numberFieldRealMatrixAt w (numberFieldMatrixBaseChange M) =
      numberFieldRealOrderMatrixAt w M := by
  rfl

omit [NumberField K] in
@[simp]
theorem numberFieldComplexMatrixAt_baseChange
    (w : {w : InfinitePlace K // w.IsComplex})
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) :
    numberFieldComplexMatrixAt w (numberFieldMatrixBaseChange M) =
      numberFieldComplexOrderMatrixAt w M := by
  rfl

omit [NumberField K] in
/-- Rational congruence restricted along scalar extension is the integral cone action. -/
theorem numberFieldArchimedeanRationalConj_baseChange
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (A : numberFieldArchimedeanForms K n) :
    numberFieldArchimedeanRationalConj
        (numberFieldMatrixBaseChange
          (g : Matrix (Fin n) (Fin n) (𝓞 K))) A =
      numberFieldArchimedeanConj g A := by
  apply Prod.ext <;> funext w <;> apply Subtype.ext <;>
    rfl

omit [NumberField K] in
/-- Rational special-linear action restricts exactly to the established integral action. -/
theorem numberFieldSpecialLinearBaseChange_smul
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (A : numberFieldArchimedeanPositiveForms K n) :
    numberFieldSpecialLinearBaseChange g • A = g • A := by
  apply Subtype.ext
  exact numberFieldArchimedeanRationalConj_baseChange g A.1

/-- Transposed determinant-one cusp frame as a rational special-linear element. -/
def numberFieldRankTwoCuspSpecialLinear
    (v : Fin 2 → K) (hv : v ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨(numberFieldRankTwoCuspFrame K v hv).transpose, by
    rw [Matrix.det_transpose, numberFieldRankTwoCuspFrame_det]⟩

/-- Rank-two cusp chart is the rational special-linear action of its cusp frame. -/
@[simp]
theorem numberFieldRankTwoCuspSpecialLinear_smul
    (v : Fin 2 → K) (hv : v ≠ 0)
    (A : numberFieldArchimedeanPositiveForms K 2) :
    numberFieldRankTwoCuspSpecialLinear v hv • A =
      numberFieldRankTwoCuspChart v hv A := rfl

end

end GaloisForLFunctions.HTGeometry

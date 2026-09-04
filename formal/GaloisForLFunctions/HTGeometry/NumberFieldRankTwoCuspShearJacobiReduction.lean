import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoCuspUnitIntegralAction

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Jacobi data transported by a rational transposed upper shear. -/
def numberFieldRankTwoArchimedeanJacobiUpperShear
    (A : numberFieldArchimedeanPositiveForms K 2)
    (J : NumberFieldArchimedeanJacobiData A) (a : K) :
    NumberFieldArchimedeanJacobiData
      (numberFieldRankTwoUpperShearTransposeSpecialLinear a • A) where
  realU w := J.realU w * numberFieldRealMatrixAt w (numberFieldRankTwoUpperShear a)
  realD := J.realD
  realPos := J.realPos
  realUpper w := by
    let hJ : IsUnipotentUpper (J.realU w) := ⟨J.realUpper w, J.realUnit w⟩
    have hE : IsUnipotentUpper
        (numberFieldRealMatrixAt w (numberFieldRankTwoUpperShear a)) := by
      constructor
      · intro i j hji
        fin_cases i <;> fin_cases j <;>
          simp [numberFieldRealMatrixAt, numberFieldRankTwoUpperShear] at hji ⊢
      · intro i
        fin_cases i <;> simp [numberFieldRealMatrixAt, numberFieldRankTwoUpperShear]
    exact (hJ.mul hE).1
  realUnit w := by
    let hJ : IsUnipotentUpper (J.realU w) := ⟨J.realUpper w, J.realUnit w⟩
    have hE : IsUnipotentUpper
        (numberFieldRealMatrixAt w (numberFieldRankTwoUpperShear a)) := by
      constructor
      · intro i j hji
        fin_cases i <;> fin_cases j <;>
          simp [numberFieldRealMatrixAt, numberFieldRankTwoUpperShear] at hji ⊢
      · intro i
        fin_cases i <;> simp [numberFieldRealMatrixAt, numberFieldRankTwoUpperShear]
    exact (hJ.mul hE).2
  realForm w := by
    let E := numberFieldRealMatrixAt w (numberFieldRankTwoUpperShear a)
    change
      (let G := numberFieldRealMatrixAt w (numberFieldRankTwoUpperShear a).transpose
       G * (A.1.1 w : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.conjTranspose G) = _
    rw [show numberFieldRealMatrixAt w (numberFieldRankTwoUpperShear a).transpose =
      E.transpose by rfl, J.realForm w]
    dsimp only [E]
    have hEt :
        Matrix.conjTranspose
            ((numberFieldRealMatrixAt w (numberFieldRankTwoUpperShear a)).transpose) =
          numberFieldRealMatrixAt w (numberFieldRankTwoUpperShear a) := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    rw [hEt, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  complexU w := J.complexU w * Matrix.conjTranspose
    (numberFieldComplexMatrixAt w (numberFieldRankTwoUpperShear a)).transpose
  complexD := J.complexD
  complexPos := J.complexPos
  complexUpper w := by
    intro i j hji
    have hi : i = (1 : Fin 2) := Fin.ext (by omega)
    have hj : j = (0 : Fin 2) := Fin.ext (by omega)
    subst i
    subst j
    simp [Matrix.mul_apply, Fin.sum_univ_two, numberFieldComplexMatrixAt,
      numberFieldRankTwoUpperShear, Matrix.conjTranspose_apply,
      Matrix.transpose_apply, J.complexUpper w 1 0 (by omega)]
  complexUnit w := by
    intro i
    fin_cases i
    · simp [Matrix.mul_apply, Fin.sum_univ_two, numberFieldComplexMatrixAt,
        numberFieldRankTwoUpperShear, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, J.complexUnit]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, numberFieldComplexMatrixAt,
        numberFieldRankTwoUpperShear, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, J.complexUnit,
        J.complexUpper w 1 0 (by omega)]
  complexForm w := by
    let E := numberFieldComplexMatrixAt w (numberFieldRankTwoUpperShear a)
    change
      (let G := numberFieldComplexMatrixAt w (numberFieldRankTwoUpperShear a).transpose
       G * (A.1.2 w : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.conjTranspose G) = _
    rw [show numberFieldComplexMatrixAt w (numberFieldRankTwoUpperShear a).transpose =
      E.transpose by rfl, J.complexForm w]
    dsimp only [E]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]

omit [NumberField K] in
@[simp]
theorem numberFieldRankTwoArchimedeanJacobiUpperShear_realU_zero_one
    (A : numberFieldArchimedeanPositiveForms K 2)
    (J : NumberFieldArchimedeanJacobiData A) (a : K)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (numberFieldRankTwoArchimedeanJacobiUpperShear A J a).realU w 0 1 =
      J.realU w 0 1 + w.1.embedding_of_isReal w.2 a := by
  simp [numberFieldRankTwoArchimedeanJacobiUpperShear,
    numberFieldRealMatrixAt, numberFieldRankTwoUpperShear,
    Matrix.mul_apply, Fin.sum_univ_two, J.realUnit]
  ring

omit [NumberField K] in
@[simp]
theorem numberFieldRankTwoArchimedeanJacobiUpperShear_complexU_zero_one
    (A : numberFieldArchimedeanPositiveForms K 2)
    (J : NumberFieldArchimedeanJacobiData A) (a : K)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (numberFieldRankTwoArchimedeanJacobiUpperShear A J a).complexU w 0 1 =
      J.complexU w 0 1 + star (w.1.embedding a) := by
  simp [numberFieldRankTwoArchimedeanJacobiUpperShear,
    numberFieldComplexMatrixAt, numberFieldRankTwoUpperShear,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, J.complexUnit]
  ring

omit [NumberField K] in
@[simp]
theorem numberFieldRankTwoArchimedeanJacobiUpperShear_weight
    (A : numberFieldArchimedeanPositiveForms K 2)
    (J : NumberFieldArchimedeanJacobiData A) (a : K)
    (i : Fin 2) (w : InfinitePlace K) :
    numberFieldArchimedeanJacobiWeight
        (numberFieldRankTwoArchimedeanJacobiUpperShear A J a) i w =
      numberFieldArchimedeanJacobiWeight J i w := by
  rw [numberFieldArchimedeanJacobiWeight,
    numberFieldArchimedeanJacobiWeight]
  split_ifs <;> simp [numberFieldRankTwoArchimedeanJacobiUpperShear]

/-- The finite cusp family admits one uniform size-reduction radius using exactly its required
`I⁻²` shear coefficients. -/
theorem exists_uniform_numberFieldRankTwoCuspJacobiUpperShearReduction
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : numberFieldRankTwoCuspType K)
      (A : numberFieldArchimedeanPositiveForms K 2)
      (J : NumberFieldArchimedeanJacobiData A),
      ∃ a : K, a ∈ numberFieldRankTwoCuspShearIdeal c ∧
        (∀ w : {w : InfinitePlace K // w.IsReal},
          |(numberFieldRankTwoArchimedeanJacobiUpperShear A J a).realU w 0 1| ≤ C) ∧
        ∀ w : {w : InfinitePlace K // w.IsComplex},
          ‖(numberFieldRankTwoArchimedeanJacobiUpperShear A J a).complexU w 0 1‖ ≤ C := by
  obtain ⟨C, hC, hcover⟩ :=
    exists_uniform_numberFieldRankTwoCuspShearIdeal_coordinateCoveringRadius K
  refine ⟨C, hC, ?_⟩
  intro c A J
  let x : mixedEmbedding.mixedSpace K :=
    (fun w => -J.realU w 0 1, fun w => -star (J.complexU w 0 1))
  obtain ⟨a, ha, hreal, hcomplex⟩ := hcover c x
  refine ⟨a, ha, ?_, ?_⟩
  · intro w
    rw [numberFieldRankTwoArchimedeanJacobiUpperShear_realU_zero_one]
    have h := hreal w
    dsimp [x] at h
    simpa only [sub_eq_add_neg, ← neg_add, abs_neg] using h
  · intro w
    rw [numberFieldRankTwoArchimedeanJacobiUpperShear_complexU_zero_one]
    have h := hcomplex w
    dsimp [x] at h
    let z : ℂ := J.complexU w 0 1
    let b : ℂ := w.1.embedding a
    change ‖z + star b‖ ≤ C
    change ‖-star z - b‖ ≤ C at h
    calc
      ‖z + star b‖ = ‖star (z + star b)‖ :=
        (norm_star _).symm
      _ = ‖star z + b‖ := by
        apply congrArg norm
        calc
          star (z + star b) = star z + star (star b) :=
            map_add (starRingEnd ℂ) z (star b)
          _ = star z + b := by rw [star_star]
      _ = ‖-star z - b‖ := by
        rw [show -star z - b = -(star z + b) by ring, norm_neg]
      _ ≤ C := h

end

end GaloisForLFunctions.HTGeometry

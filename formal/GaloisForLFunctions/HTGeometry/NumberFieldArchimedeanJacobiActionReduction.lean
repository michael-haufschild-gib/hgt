import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobiSizeReduction

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

omit [NumberField K] in
theorem numberFieldRealOrderMatrixAt_transpose
    (w : {w : InfinitePlace K // w.IsReal})
    (N : Matrix (Fin n) (Fin n) (𝓞 K)) :
    numberFieldRealOrderMatrixAt w Nᵀ =
      (numberFieldRealOrderMatrixAt w N)ᵀ := by
  rfl

omit [NumberField K] in
theorem numberFieldComplexOrderMatrixAt_transpose
    (w : {w : InfinitePlace K // w.IsComplex})
    (N : Matrix (Fin n) (Fin n) (𝓞 K)) :
    numberFieldComplexOrderMatrixAt w Nᵀ =
      (numberFieldComplexOrderMatrixAt w N)ᵀ := by
  rfl

def numberFieldTransposeSpecialLinear
    (N : Matrix (Fin n) (Fin n) (𝓞 K)) (hN : N.det = 1) :
    Matrix.SpecialLinearGroup (Fin n) (𝓞 K) :=
  ⟨Nᵀ, by simpa using hN⟩

omit [NumberField K] in
theorem numberFieldRealOrderMatrixAt_unipotentUpper
    (N : Matrix (Fin n) (Fin n) (𝓞 K))
    (hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N))
    (w : {w : InfinitePlace K // w.IsReal}) :
    IsUnipotentUpper (numberFieldRealOrderMatrixAt w N) := by
  constructor
  · intro i j hji
    have h := congrArg (fun x : mixedEmbedding.mixedSpace K => x.1 w)
      (hN.upper i j hji)
    exact h
  · intro i
    have h := congrArg (fun x : mixedEmbedding.mixedSpace K => x.1 w)
      (hN.unit i)
    exact h

omit [NumberField K] in
theorem numberFieldComplexOrderMatrixAt_upper
    (N : Matrix (Fin n) (Fin n) (𝓞 K))
    (hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    ∀ i j, j < i → numberFieldComplexOrderMatrixAt w N i j = 0 := by
  intro i j hji
  have h := congrArg (fun x : mixedEmbedding.mixedSpace K => x.2 w)
    (hN.upper i j hji)
  exact h

omit [NumberField K] in
theorem numberFieldComplexOrderMatrixAt_unit
    (N : Matrix (Fin n) (Fin n) (𝓞 K))
    (hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    ∀ i, numberFieldComplexOrderMatrixAt w N i i = 1 := by
  intro i
  have h := congrArg (fun x : mixedEmbedding.mixedSpace K => x.2 w)
    (hN.unit i)
  exact h

omit [NumberField K] in
def numberFieldArchimedeanJacobiTransposeConj
    (A : numberFieldArchimedeanPositiveForms K n)
    (J : NumberFieldArchimedeanJacobiData A)
    (N : Matrix (Fin n) (Fin n) (𝓞 K)) (hdet : N.det = 1)
    (hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N)) :
    NumberFieldArchimedeanJacobiData
      ((numberFieldTransposeSpecialLinear N hdet) • A) where
  realU w := J.realU w * numberFieldRealOrderMatrixAt w N
  realD := J.realD
  realPos := J.realPos
  realUpper w := by
    let hJ : IsUnipotentUpper (J.realU w) := ⟨J.realUpper w, J.realUnit w⟩
    exact (hJ.mul (numberFieldRealOrderMatrixAt_unipotentUpper N hN w)).1
  realUnit w := by
    let hJ : IsUnipotentUpper (J.realU w) := ⟨J.realUpper w, J.realUnit w⟩
    exact (hJ.mul (numberFieldRealOrderMatrixAt_unipotentUpper N hN w)).2
  realForm w := by
    let E := numberFieldRealOrderMatrixAt w N
    change
      ((numberFieldArchimedeanConj (numberFieldTransposeSpecialLinear N hdet) A.1).1 w :
          Matrix (Fin n) (Fin n) ℝ) = _
    rw [show ((numberFieldArchimedeanConj
          (numberFieldTransposeSpecialLinear N hdet) A.1).1 w :
          Matrix (Fin n) (Fin n) ℝ) =
        let G := numberFieldRealOrderMatrixAt w Nᵀ
        G * (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) * Gᴴ by rfl]
    rw [numberFieldRealOrderMatrixAt_transpose, J.realForm w]
    dsimp only [E]
    have hEt : ((numberFieldRealOrderMatrixAt w N)ᵀ)ᴴ =
        numberFieldRealOrderMatrixAt w N := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    rw [hEt, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  complexU w := J.complexU w * (numberFieldComplexOrderMatrixAt w N)ᵀᴴ
  complexD := J.complexD
  complexPos := J.complexPos
  complexUpper w := by
    intro i j hji
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : k < i
    · rw [J.complexUpper w i k hki, zero_mul]
    · have hjk : j < k := lt_of_lt_of_le hji (not_lt.1 hki)
      rw [Matrix.conjTranspose_apply, Matrix.transpose_apply,
        numberFieldComplexOrderMatrixAt_upper N hN w k j hjk]
      simp
  complexUnit w := by
    intro i
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_single i (fun k _ hki => ?_)
      (fun hcon => absurd (Finset.mem_univ i) hcon)).trans ?_
    · rcases lt_or_gt_of_ne hki with hlt | hgt
      · rw [J.complexUpper w i k hlt, zero_mul]
      · rw [Matrix.conjTranspose_apply, Matrix.transpose_apply,
          numberFieldComplexOrderMatrixAt_upper N hN w k i hgt]
        simp
    · rw [J.complexUnit w i, Matrix.conjTranspose_apply, Matrix.transpose_apply,
        numberFieldComplexOrderMatrixAt_unit N hN w i]
      simp
  complexForm w := by
    let E := numberFieldComplexOrderMatrixAt w N
    change
      ((numberFieldArchimedeanConj (numberFieldTransposeSpecialLinear N hdet) A.1).2 w :
          Matrix (Fin n) (Fin n) ℂ) = _
    rw [show ((numberFieldArchimedeanConj
          (numberFieldTransposeSpecialLinear N hdet) A.1).2 w :
          Matrix (Fin n) (Fin n) ℂ) =
        let G := numberFieldComplexOrderMatrixAt w Nᵀ
        G * (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) * Gᴴ by rfl]
    rw [numberFieldComplexOrderMatrixAt_transpose, J.complexForm w]
    dsimp only [E]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]

theorem exists_numberFieldArchimedeanJacobi_actionSizeReductionRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ)
      (A : numberFieldArchimedeanPositiveForms K n),
      ∃ g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K),
        ∃ J' : NumberFieldArchimedeanJacobiData (g • A),
          (∀ w i j, i < j → |J'.realU w i j| ≤ C) ∧
          ∀ w i j, i < j → ‖J'.complexU w i j‖ ≤ C := by
  obtain ⟨C, hC, hreduce⟩ :=
    exists_numberFieldArchimedeanJacobi_sizeReductionRadius K
  refine ⟨C, hC, ?_⟩
  intro n A
  let J : NumberFieldArchimedeanJacobiData A :=
    Classical.choice (exists_numberFieldArchimedeanJacobiData A)
  obtain ⟨N, hdet, hN, hreal, hcomplex⟩ := hreduce n A J
  let g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) :=
    numberFieldTransposeSpecialLinear N hdet
  let J' : NumberFieldArchimedeanJacobiData (g • A) :=
    numberFieldArchimedeanJacobiTransposeConj A J N hdet hN
  exact ⟨g, J', hreal, hcomplex⟩

end

end GaloisForLFunctions.HTGeometry

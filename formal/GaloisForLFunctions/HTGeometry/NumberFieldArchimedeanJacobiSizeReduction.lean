import GaloisForLFunctions.HTGeometry.NumberFieldMixedSizeReduction
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobiReduction

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

omit [NumberField K] in
def mixedRealEval (w : {w : InfinitePlace K // w.IsReal}) :
    mixedEmbedding.mixedSpace K →+ ℝ where
  toFun x := x.1 w
  map_zero' := rfl
  map_add' _ _ := rfl

omit [NumberField K] in
def mixedComplexEval (w : {w : InfinitePlace K // w.IsComplex}) :
    mixedEmbedding.mixedSpace K →+ ℂ where
  toFun x := x.2 w
  map_zero' := rfl
  map_add' _ _ := rfl

def numberFieldArchimedeanJacobiMixedU
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) :
    Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) :=
  fun i j =>
    (fun w => J.realU w i j, fun w => star (J.complexU w i j))

omit [NumberField K] in
theorem numberFieldArchimedeanJacobiMixedU_unipotentUpper
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) :
    IsMixedUnipotentUpper (numberFieldArchimedeanJacobiMixedU J) := by
  constructor
  · intro i j hji
    apply Prod.ext <;> funext w
    · exact J.realUpper w i j hji
    · simp [numberFieldArchimedeanJacobiMixedU, J.complexUpper w i j hji]
  · intro i
    apply Prod.ext <;> funext w
    · exact J.realUnit w i
    · simp [numberFieldArchimedeanJacobiMixedU, J.complexUnit w i]

omit [NumberField K] in
theorem numberFieldArchimedeanJacobiMixedU_mul_real
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (N : Matrix (Fin n) (Fin n) (𝓞 K))
    (w : {w : InfinitePlace K // w.IsReal}) (i j : Fin n) :
    ((numberFieldArchimedeanJacobiMixedU J *
        numberFieldMixedOrderMatrix N) i j).1 w =
      (J.realU w * numberFieldRealOrderMatrixAt w N) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  change mixedRealEval w (∑ x, numberFieldArchimedeanJacobiMixedU J i x *
    numberFieldMixedOrderMatrix N x j) = _
  rw [map_sum]
  rfl

omit [NumberField K] in
theorem numberFieldArchimedeanJacobiMixedU_mul_complex
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (N : Matrix (Fin n) (Fin n) (𝓞 K))
    (w : {w : InfinitePlace K // w.IsComplex}) (i j : Fin n) :
    ((numberFieldArchimedeanJacobiMixedU J *
        numberFieldMixedOrderMatrix N) i j).2 w =
      star ((J.complexU w *
        (numberFieldComplexOrderMatrixAt w N)ᵀᴴ) i j) := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  change mixedComplexEval w (∑ x, numberFieldArchimedeanJacobiMixedU J i x *
    numberFieldMixedOrderMatrix N x j) = _
  rw [map_sum]
  simp [mixedComplexEval, numberFieldArchimedeanJacobiMixedU, numberFieldMixedOrderMatrix,
    numberFieldComplexOrderMatrixAt, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    star_sum]

theorem norm_pi_apply_le {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)]
    (f : ∀ i, E i) (i : ι) : ‖f i‖ ≤ ‖f‖ := by
  rw [Pi.norm_def]
  exact NNReal.coe_le_coe.mpr
    (Finset.le_sup (f := fun b => ‖f b‖₊) (Finset.mem_univ i))

theorem norm_mixed_real_apply_le
    (x : mixedEmbedding.mixedSpace K)
    (w : {w : InfinitePlace K // w.IsReal}) : ‖x.1 w‖ ≤ ‖x‖ :=
  (norm_pi_apply_le x.1 w).trans (norm_fst_le x)

theorem norm_mixed_complex_apply_le
    (x : mixedEmbedding.mixedSpace K)
    (w : {w : InfinitePlace K // w.IsComplex}) : ‖x.2 w‖ ≤ ‖x‖ :=
  (norm_pi_apply_le x.2 w).trans (norm_snd_le x)

theorem exists_numberFieldArchimedeanJacobi_sizeReductionRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ)
      (A : numberFieldArchimedeanPositiveForms K n)
      (J : NumberFieldArchimedeanJacobiData A),
      ∃ N : Matrix (Fin n) (Fin n) (𝓞 K),
        N.det = 1 ∧
        IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N) ∧
        (∀ w i j, i < j →
          |(J.realU w * numberFieldRealOrderMatrixAt w N) i j| ≤ C) ∧
        ∀ w i j, i < j →
          ‖(J.complexU w * (numberFieldComplexOrderMatrixAt w N)ᵀᴴ) i j‖ ≤ C := by
  obtain ⟨C, hC, hreduce⟩ :=
    exists_numberFieldMixed_unipotentUpperReduction K
  refine ⟨C, hC, ?_⟩
  intro n A J
  obtain ⟨N, hdet, hN, hbound⟩ :=
    hreduce n (numberFieldArchimedeanJacobiMixedU J)
      (numberFieldArchimedeanJacobiMixedU_unipotentUpper J)
  refine ⟨N, hdet, hN, ?_, ?_⟩
  · intro w i j hij
    rw [← Real.norm_eq_abs,
      ← numberFieldArchimedeanJacobiMixedU_mul_real J N w i j]
    exact (norm_mixed_real_apply_le _ w).trans (hbound i j hij)
  · intro w i j hij
    rw [← norm_star,
      ← numberFieldArchimedeanJacobiMixedU_mul_complex J N w i j]
    exact (norm_mixed_complex_apply_le _ w).trans (hbound i j hij)

end

end GaloisForLFunctions.HTGeometry

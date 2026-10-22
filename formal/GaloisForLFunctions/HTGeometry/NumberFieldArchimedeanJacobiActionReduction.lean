import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobiSizeReduction

/-!
# Size reduction of Jacobi coordinates by the action of `SL_n(𝓞 K)`

For a number field `K`, a positive archimedean form `A` is a positive-definite real symmetric
matrix at every real place and a positive-definite Hermitian matrix at every complex place, with
`SL_n(𝓞 K)` acting by placewise congruence. If `A = Uᵀ D U` (resp. `Uᴴ D U`) is a simultaneous
Jacobi decomposition and `N` is a determinant-one integral matrix whose mixed embedding is
unipotent upper triangular, then acting by `Nᵀ` transports the Jacobi data to `U N` with the same
diagonal. Combined with the mixed size-reduction theorem, every positive archimedean form lies in
the `SL_n(𝓞 K)`-orbit of a form with Jacobi data whose strictly upper unipotent entries are bounded
by a constant depending only on `K`.

## Main results

- `numberFieldArchimedeanJacobiTransposeConj`: Jacobi data for `Nᵀ • A`, obtained by
  right-multiplying the unipotent parts by the place evaluations of `N`.
- `exists_numberFieldArchimedeanJacobi_actionSizeReductionRadius`: there is `C ≥ 0` depending
  only on `K` such that every positive archimedean form `A` has some `g ∈ SL_n(𝓞 K)` and Jacobi
  data for `g • A` with all strictly upper unipotent entries of absolute value at most `C`, at
  every real and complex place.

## Hypotheses

The main theorem is unconditional. The transport construction takes as inputs `det N = 1` and
the unipotent upper triangularity of the mixed embedding of `N`, both genuine properties of the
matrix being acted with.
-/

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

/-- The transpose `Nᵀ` of a determinant-one integral matrix, as an element of `SL_n(𝓞 K)`. -/
def numberFieldTransposeSpecialLinear
    (N : Matrix (Fin n) (Fin n) (𝓞 K)) (hN : N.det = 1) :
    Matrix.SpecialLinearGroup (Fin n) (𝓞 K) :=
  ⟨Nᵀ, by simpa using hN⟩

omit [NumberField K] in
/-- If the mixed embedding of `N` is unipotent upper triangular, so is its evaluation at each
real place. -/
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
/-- Given Jacobi data `A = Uᵀ D U` (real places) and `Uᴴ D U` (complex places) and an integral
`N` with `det N = 1` and unipotent upper mixed embedding, Jacobi data for `Nᵀ • A` with unipotent
parts `U N_w` (real) and `U (N_wᵀ)ᴴ` (complex) and the same diagonals. -/
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

/-- Size reduction in the orbit: there is `C ≥ 0` depending only on `K` such that every positive
archimedean form `A` admits `g ∈ SL_n(𝓞 K)` and Jacobi data for `g • A` whose strictly upper
unipotent entries are bounded by `C` at every real and complex place. -/
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

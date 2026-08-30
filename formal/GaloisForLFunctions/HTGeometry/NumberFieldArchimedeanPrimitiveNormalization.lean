import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanPrimitiveMinimum

/-!
# Primitive normalization for the archimedean cone

A primitive minimizer is completed to a determinant-one integral matrix and transported by the
existing row-congruence action.  The transpose is forced by the first-column completion.  At
complex places, the adjoint sends the conjugated embedded vector to the conjugate of the exact
integral matrix product, so row-Hermitian energy is equivariant without any embedding premise.

Consequently the normalized first coordinate has no greater total archimedean energy than any
other coordinate.  All primitive, invertibility, determinant, and embedding obligations are
discharged internally.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder Matrix NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Transpose a determinant-one integral matrix into the special-linear cone action. -/
def transposeSpecialLinearOfDetOne
    (β : Matrix (Fin n) (Fin n) (𝓞 K)) (hβ : β.det = 1) :
    Matrix.SpecialLinearGroup (Fin n) (𝓞 K) :=
  ⟨βᵀ, by rw [Matrix.det_transpose, hβ]⟩

omit [NumberField K] in
@[simp]
theorem coe_transposeSpecialLinearOfDetOne
    (β : Matrix (Fin n) (Fin n) (𝓞 K)) (hβ : β.det = 1) :
    (transposeSpecialLinearOfDetOne β hβ : Matrix (Fin n) (Fin n) (𝓞 K)) = βᵀ := rfl

/-- Real components of the integral mixed embedding are the selected real embeddings. -/
@[simp]
theorem numberFieldIntegerVectorEmbedding_real_apply
    (a : Fin n → 𝓞 K) (i : Fin n)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (numberFieldIntegerVectorEmbedding K a i).1 w =
      (w.1.embedding_of_isReal w.2) (a i : K) := rfl

/-- Complex components of the integral mixed embedding are the selected complex embeddings. -/
@[simp]
theorem numberFieldIntegerVectorEmbedding_complex_apply
    (a : Fin n → 𝓞 K) (i : Fin n)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (numberFieldIntegerVectorEmbedding K a i).2 w =
      w.1.embedding (a i : K) := rfl

/-- At a real place, the adjoint transposed action realizes the integral matrix product. -/
theorem numberFieldReal_transposeSpecialLinear_adjoint_mulVec_embedding
    (β : Matrix (Fin n) (Fin n) (𝓞 K)) (hβ : β.det = 1)
    (b : Fin n → 𝓞 K) (w : {w : InfinitePlace K // w.IsReal}) :
    (numberFieldRealOrderMatrixAt w
      (transposeSpecialLinearOfDetOne β hβ : Matrix (Fin n) (Fin n) (𝓞 K)))ᴴ.mulVec
        (fun i => (numberFieldIntegerVectorEmbedding K b i).1 w) =
      fun i => (numberFieldIntegerVectorEmbedding K (β.mulVec b) i).1 w := by
  funext i
  simp [transposeSpecialLinearOfDetOne, numberFieldRealOrderMatrixAt,
    numberFieldIntegerVectorEmbedding, Matrix.mulVec, Matrix.conjTranspose_apply,
    mixedEmbedding]
  let φ : 𝓞 K →+* ℝ :=
    (w.1.embedding_of_isReal w.2).comp (algebraMap (𝓞 K) K)
  change (∑ j, φ (β i j) * φ (b j)) = φ (∑ j, β i j * b j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]

/-- At a complex place, the adjoint transposed action realizes the conjugated integral product. -/
theorem numberFieldComplex_transposeSpecialLinear_adjoint_mulVec_embedding
    (β : Matrix (Fin n) (Fin n) (𝓞 K)) (hβ : β.det = 1)
    (b : Fin n → 𝓞 K) (w : {w : InfinitePlace K // w.IsComplex}) :
    (numberFieldComplexOrderMatrixAt w
      (transposeSpecialLinearOfDetOne β hβ : Matrix (Fin n) (Fin n) (𝓞 K)))ᴴ.mulVec
        (star (fun i => (numberFieldIntegerVectorEmbedding K b i).2 w)) =
      star (fun i =>
        (numberFieldIntegerVectorEmbedding K (β.mulVec b) i).2 w) := by
  funext i
  simp [transposeSpecialLinearOfDetOne, numberFieldComplexOrderMatrixAt,
    Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]

/-- Row-Hermitian archimedean energy is exactly equivariant under transposed integral action. -/
theorem numberFieldArchimedeanEnergy_transposeSpecialLinear
    (β : Matrix (Fin n) (Fin n) (𝓞 K)) (hβ : β.det = 1)
    (A : numberFieldArchimedeanPositiveForms K n)
    (b : Fin n → 𝓞 K) :
    numberFieldArchimedeanEnergy
        ((transposeSpecialLinearOfDetOne β hβ) • A)
        (numberFieldIntegerVectorEmbedding K b) =
      numberFieldArchimedeanEnergy A
        (numberFieldIntegerVectorEmbedding K (β.mulVec b)) := by
  unfold numberFieldArchimedeanEnergy
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro w hw
    let G := numberFieldRealOrderMatrixAt w
      (transposeSpecialLinearOfDetOne β hβ : Matrix (Fin n) (Fin n) (𝓞 K))
    let M := (A.1.1 w : Matrix (Fin n) (Fin n) ℝ)
    let z := fun i => (numberFieldIntegerVectorEmbedding K b i).1 w
    let c := fun i =>
      (numberFieldIntegerVectorEmbedding K (β.mulVec b) i).1 w
    change z ⬝ᵥ (G * M * Gᴴ).mulVec z = c ⬝ᵥ M.mulVec c
    have hcongr := star_dotProduct_real_congr_mulVec M Gᴴ z
    rw [Matrix.conjTranspose_conjTranspose] at hcongr
    have hc : Gᴴ.mulVec z = c := by
      exact numberFieldReal_transposeSpecialLinear_adjoint_mulVec_embedding β hβ b w
    rw [hc] at hcongr
    simpa only [star_trivial] using hcongr
  · apply Finset.sum_congr rfl
    intro w hw
    let G := numberFieldComplexOrderMatrixAt w
      (transposeSpecialLinearOfDetOne β hβ : Matrix (Fin n) (Fin n) (𝓞 K))
    let M := (A.1.2 w : Matrix (Fin n) (Fin n) ℂ)
    let z := fun i => (numberFieldIntegerVectorEmbedding K b i).2 w
    let c := fun i =>
      (numberFieldIntegerVectorEmbedding K (β.mulVec b) i).2 w
    change (z ⬝ᵥ (G * M * Gᴴ).mulVec (star z)).re =
      (c ⬝ᵥ M.mulVec (star c)).re
    have hcongr := star_dotProduct_complex_square_congr_mulVec M G (star z)
    have hc : Gᴴ.mulVec (star z) = star c := by
      exact numberFieldComplex_transposeSpecialLinear_adjoint_mulVec_embedding β hβ b w
    rw [hc] at hcongr
    have hre := congrArg Complex.re hcongr
    simpa using hre

/-- Standard integral coordinate vector. -/
def numberFieldCoordinateBasis (j : Fin n) : Fin n → 𝓞 K :=
  Pi.single j 1

omit [NumberField K] in
/-- Every standard coordinate vector is primitive. -/
theorem numberFieldCoordinateBasis_primitive (j : Fin n) :
    ∃ p : Fin n → 𝓞 K,
      ∑ i, p i * numberFieldCoordinateBasis (K := K) j i = 1 := by
  refine ⟨numberFieldCoordinateBasis (K := K) j, ?_⟩
  rw [Finset.sum_eq_single j]
  · simp [numberFieldCoordinateBasis]
  · intro i hi hij
    simp [numberFieldCoordinateBasis, hij]
  · simp

omit [NumberField K] in
/-- Multiplying a standard coordinate vector selects the corresponding column. -/
theorem mulVec_numberFieldCoordinateBasis
    (β : Matrix (Fin n) (Fin n) (𝓞 K)) (j : Fin n) :
    β.mulVec (numberFieldCoordinateBasis (K := K) j) = fun i => β i j := by
  funext i
  rw [numberFieldCoordinateBasis, Matrix.mulVec_single]
  simp

omit [NumberField K] in
/-- Every column of a determinant-one matrix over the number ring is primitive. -/
theorem detOne_column_primitive
    (β : Matrix (Fin n) (Fin n) (𝓞 K)) (hβ : β.det = 1)
    (j : Fin n) :
    ∃ p : Fin n → 𝓞 K, ∑ i, p i * β i j = 1 := by
  have hu : IsUnit β.det := by rw [hβ]; exact isUnit_one
  have hinv := Matrix.nonsing_inv_mul β hu
  have hj := congrFun (congrFun hinv j) j
  refine ⟨fun i => β⁻¹ j i, ?_⟩
  simpa [Matrix.mul_apply] using hj

omit [NumberField K] in
/-- A determinant-one matrix sends every standard coordinate vector to a primitive vector. -/
theorem detOne_mulVec_coordinateBasis_primitive
    (β : Matrix (Fin n) (Fin n) (𝓞 K)) (hβ : β.det = 1)
    (j : Fin n) :
    ∃ p : Fin n → 𝓞 K,
      ∑ i, p i * (β.mulVec (numberFieldCoordinateBasis (K := K) j)) i = 1 := by
  rw [mulVec_numberFieldCoordinateBasis]
  exact detOne_column_primitive β hβ j

/-- Every corrected archimedean form has an integral special-linear normalization whose first
coordinate has minimum total energy among all coordinate vectors. -/
theorem exists_numberFieldArchimedean_primitiveNormalization
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 2 ≤ n)
    (A : numberFieldArchimedeanPositiveForms K n) :
    ∃ (a : Fin n → 𝓞 K) (β : Matrix (Fin n) (Fin n) (𝓞 K))
        (hβ : β.det = 1),
      (∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1) ∧
      (∀ i, β i ⟨0, lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ = a i) ∧
      ∀ j : Fin n,
        numberFieldArchimedeanEnergy
            ((transposeSpecialLinearOfDetOne β hβ) • A)
            (numberFieldIntegerVectorEmbedding K
              (numberFieldCoordinateBasis (K := K)
                ⟨0, lt_of_lt_of_le (Nat.succ_pos 1) hn⟩)) ≤
          numberFieldArchimedeanEnergy
            ((transposeSpecialLinearOfDetOne β hβ) • A)
            (numberFieldIntegerVectorEmbedding K
              (numberFieldCoordinateBasis (K := K) j)) := by
  obtain ⟨a, β, hprim, hmin, hβ, hcol⟩ :=
    exists_numberFieldArchimedean_minimalPrimitiveVector K n hn A
  refine ⟨a, β, hβ, hprim, hcol, ?_⟩
  intro j
  rw [numberFieldArchimedeanEnergy_transposeSpecialLinear,
    numberFieldArchimedeanEnergy_transposeSpecialLinear]
  have hzero : β.mulVec
      (numberFieldCoordinateBasis (K := K)
        ⟨0, lt_of_lt_of_le (Nat.succ_pos 1) hn⟩) = a := by
    rw [mulVec_numberFieldCoordinateBasis]
    funext i
    exact hcol i
  rw [hzero]
  exact hmin _ (detOne_mulVec_coordinateBasis_primitive β hβ j)

end

end GaloisForLFunctions.HTGeometry

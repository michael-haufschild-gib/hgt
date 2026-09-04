import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanPrimitiveNormalization
import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoCuspFrame

/-!
# Rational cusp charts on the number-field archimedean cone

A nonprincipal projective cusp cannot be moved to the standard coordinate line by an integral
special-linear matrix.  Its determinant-one pseudo-basis frame is nevertheless a matrix over the
number field.  This file builds the corresponding placewise real/Hermitian congruence, proves that
it preserves the corrected positive cone, and identifies the first-coordinate energy of the
transposed cusp chart with the energy of the cusp vector itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder Matrix NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Evaluate a number-field matrix at a real infinite place. -/
def numberFieldRealMatrixAt (w : {w : InfinitePlace K // w.IsReal})
    (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) ℝ :=
  (w.1.embedding_of_isReal w.2).mapMatrix M

/-- Evaluate a number-field matrix at a chosen complex embedding. -/
def numberFieldComplexMatrixAt (w : {w : InfinitePlace K // w.IsComplex})
    (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) ℂ :=
  w.1.embedding.mapMatrix M

omit [NumberField K] in
@[simp]
theorem numberFieldRealMatrixAt_one
    (w : {w : InfinitePlace K // w.IsReal}) :
    numberFieldRealMatrixAt w (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  exact map_one _

omit [NumberField K] in
@[simp]
theorem numberFieldComplexMatrixAt_one
    (w : {w : InfinitePlace K // w.IsComplex}) :
    numberFieldComplexMatrixAt w (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  exact map_one _

omit [NumberField K] in
@[simp]
theorem numberFieldRealMatrixAt_mul
    (w : {w : InfinitePlace K // w.IsReal})
    (M N : Matrix (Fin n) (Fin n) K) :
    numberFieldRealMatrixAt w (M * N) =
      numberFieldRealMatrixAt w M * numberFieldRealMatrixAt w N := by
  exact map_mul _ _ _

omit [NumberField K] in
@[simp]
theorem numberFieldComplexMatrixAt_mul
    (w : {w : InfinitePlace K // w.IsComplex})
    (M N : Matrix (Fin n) (Fin n) K) :
    numberFieldComplexMatrixAt w (M * N) =
      numberFieldComplexMatrixAt w M * numberFieldComplexMatrixAt w N := by
  exact map_mul _ _ _

omit [NumberField K] in
theorem numberFieldRealMatrixAt_det
    (w : {w : InfinitePlace K // w.IsReal})
    (M : Matrix (Fin n) (Fin n) K) :
    (numberFieldRealMatrixAt w M).det = w.1.embedding_of_isReal w.2 M.det := by
  exact (RingHom.map_det _ _).symm

omit [NumberField K] in
theorem numberFieldComplexMatrixAt_det
    (w : {w : InfinitePlace K // w.IsComplex})
    (M : Matrix (Fin n) (Fin n) K) :
    (numberFieldComplexMatrixAt w M).det = w.1.embedding M.det := by
  exact (RingHom.map_det _ _).symm

/-- Placewise congruence by a number-field matrix. -/
def numberFieldArchimedeanRationalConj
    (M : Matrix (Fin n) (Fin n) K)
    (A : numberFieldArchimedeanForms K n) : numberFieldArchimedeanForms K n :=
  (fun w =>
    let G := numberFieldRealMatrixAt w M
    ⟨G * (A.1 w : Matrix (Fin n) (Fin n) ℝ) * Gᴴ, by
      change (G * (A.1 w : Matrix (Fin n) (Fin n) ℝ) * Gᴴ)ᴴ = _
      have hA : ((A.1 w : Matrix (Fin n) (Fin n) ℝ))ᴴ = A.1 w := (A.1 w).prop
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA]
      simp only [Matrix.mul_assoc]⟩,
   fun w =>
    let G := numberFieldComplexMatrixAt w M
    ⟨G * (A.2 w : Matrix (Fin n) (Fin n) ℂ) * Gᴴ, by
      change (G * (A.2 w : Matrix (Fin n) (Fin n) ℂ) * Gᴴ)ᴴ = _
      have hA : ((A.2 w : Matrix (Fin n) (Fin n) ℂ))ᴴ = A.2 w := (A.2 w).prop
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA]
      simp only [Matrix.mul_assoc]⟩)

omit [NumberField K] in
/-- Determinant-one rational congruence preserves the corrected positive cone. -/
theorem numberFieldArchimedeanRationalConj_mem
    (M : Matrix (Fin n) (Fin n) K) (hM : M.det = 1)
    {A : numberFieldArchimedeanForms K n}
    (hA : A ∈ numberFieldArchimedeanCone K n) :
    numberFieldArchimedeanRationalConj M A ∈ numberFieldArchimedeanCone K n := by
  constructor
  · intro w
    have hdet : (numberFieldRealMatrixAt w M).det = 1 := by
      rw [numberFieldRealMatrixAt_det, hM, map_one]
    have hunit : IsUnit (numberFieldRealMatrixAt w M) := by
      rw [Matrix.isUnit_iff_isUnit_det, hdet]
      exact isUnit_one
    exact (hA.1 w).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit hunit)
  · intro w
    have hdet : (numberFieldComplexMatrixAt w M).det = 1 := by
      rw [numberFieldComplexMatrixAt_det, hM, map_one]
    have hunit : IsUnit (numberFieldComplexMatrixAt w M) := by
      rw [Matrix.isUnit_iff_isUnit_det, hdet]
      exact isUnit_one
    exact (hA.2 w).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit hunit)

/-- Positive archimedean congruence by a determinant-one number-field matrix. -/
def numberFieldArchimedeanPositiveRationalConj
    (M : Matrix (Fin n) (Fin n) K) (hM : M.det = 1)
    (A : numberFieldArchimedeanPositiveForms K n) :
    numberFieldArchimedeanPositiveForms K n :=
  ⟨numberFieldArchimedeanRationalConj M A.1,
    numberFieldArchimedeanRationalConj_mem M hM A.2⟩

/-- Mixed embedding applied coordinatewise to a number-field vector. -/
def numberFieldVectorEmbedding (a : Fin n → K) :
    Fin n → mixedEmbedding.mixedSpace K :=
  fun i => mixedEmbedding K (a i)

omit [NumberField K] in
@[simp]
theorem numberFieldVectorEmbedding_real_apply
    (a : Fin n → K) (i : Fin n)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (numberFieldVectorEmbedding a i).1 w =
      w.1.embedding_of_isReal w.2 (a i) := rfl

omit [NumberField K] in
@[simp]
theorem numberFieldVectorEmbedding_complex_apply
    (a : Fin n → K) (i : Fin n)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (numberFieldVectorEmbedding a i).2 w = w.1.embedding (a i) := rfl

/-- A transposed rational matrix acts on embedded real vectors through its adjoint. -/
theorem numberFieldReal_transposeMatrix_adjoint_mulVec_embedding
    (M : Matrix (Fin n) (Fin n) K)
    (b : Fin n → K) (w : {w : InfinitePlace K // w.IsReal}) :
    (numberFieldRealMatrixAt w M.transpose)ᴴ.mulVec
        (fun i => (numberFieldVectorEmbedding b i).1 w) =
      fun i => (numberFieldVectorEmbedding (M.mulVec b) i).1 w := by
  funext i
  simp [numberFieldRealMatrixAt, numberFieldVectorEmbedding, Matrix.mulVec,
    Matrix.conjTranspose_apply, mixedEmbedding]
  let φ : K →+* ℝ := w.1.embedding_of_isReal w.2
  change (∑ j, φ (M i j) * φ (b j)) = φ (∑ j, M i j * b j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]

/-- A transposed rational matrix acts on embedded complex vectors through its adjoint. -/
theorem numberFieldComplex_transposeMatrix_adjoint_mulVec_embedding
    (M : Matrix (Fin n) (Fin n) K)
    (b : Fin n → K) (w : {w : InfinitePlace K // w.IsComplex}) :
    (numberFieldComplexMatrixAt w M.transpose)ᴴ.mulVec
        (star (fun i => (numberFieldVectorEmbedding b i).2 w)) =
      star (fun i =>
        (numberFieldVectorEmbedding (M.mulVec b) i).2 w) := by
  funext i
  simp_rw [numberFieldVectorEmbedding_complex_apply]
  simp [numberFieldComplexMatrixAt, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply]

/-- Row-Hermitian energy is equivariant under transposed rational determinant-one congruence. -/
theorem numberFieldArchimedeanEnergy_transposeRational
    (M : Matrix (Fin n) (Fin n) K) (hM : M.det = 1)
    (A : numberFieldArchimedeanPositiveForms K n)
    (b : Fin n → K) :
    numberFieldArchimedeanEnergy
        (numberFieldArchimedeanPositiveRationalConj M.transpose
          (by rw [Matrix.det_transpose, hM]) A)
        (numberFieldVectorEmbedding b) =
      numberFieldArchimedeanEnergy A
        (numberFieldVectorEmbedding (M.mulVec b)) := by
  unfold numberFieldArchimedeanEnergy
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro w hw
    let G := numberFieldRealMatrixAt w M.transpose
    let Q := (A.1.1 w : Matrix (Fin n) (Fin n) ℝ)
    let z := fun i => (numberFieldVectorEmbedding b i).1 w
    let c := fun i => (numberFieldVectorEmbedding (M.mulVec b) i).1 w
    change z ⬝ᵥ (G * Q * Gᴴ).mulVec z = c ⬝ᵥ Q.mulVec c
    have hcongr := star_dotProduct_real_congr_mulVec Q Gᴴ z
    rw [Matrix.conjTranspose_conjTranspose] at hcongr
    have hc : Gᴴ.mulVec z = c := by
      exact numberFieldReal_transposeMatrix_adjoint_mulVec_embedding M b w
    rw [hc] at hcongr
    simpa only [star_trivial] using hcongr
  · apply Finset.sum_congr rfl
    intro w hw
    let G := numberFieldComplexMatrixAt w M.transpose
    let Q := (A.1.2 w : Matrix (Fin n) (Fin n) ℂ)
    let z := fun i => (numberFieldVectorEmbedding b i).2 w
    let c := fun i => (numberFieldVectorEmbedding (M.mulVec b) i).2 w
    change (z ⬝ᵥ (G * Q * Gᴴ).mulVec (star z)).re =
      (c ⬝ᵥ Q.mulVec (star c)).re
    have hcongr := star_dotProduct_complex_square_congr_mulVec Q G (star z)
    have hc : Gᴴ.mulVec (star z) = star c := by
      exact numberFieldComplex_transposeMatrix_adjoint_mulVec_embedding M b w
    rw [hc] at hcongr
    have hre := congrArg Complex.re hcongr
    simpa using hre

/-- Rank-two cusp-frame chart of a corrected archimedean form. -/
def numberFieldRankTwoCuspChart
    (v : Fin 2 → K) (hv : v ≠ 0)
    (A : numberFieldArchimedeanPositiveForms K 2) :
    numberFieldArchimedeanPositiveForms K 2 :=
  numberFieldArchimedeanPositiveRationalConj
    (numberFieldRankTwoCuspFrame K v hv).transpose
    (by rw [Matrix.det_transpose, numberFieldRankTwoCuspFrame_det]) A

/-- First-coordinate energy in a cusp chart is the energy of its defining projective vector. -/
theorem numberFieldRankTwoCuspChart_energy_zero
    (v : Fin 2 → K) (hv : v ≠ 0)
    (A : numberFieldArchimedeanPositiveForms K 2) :
    numberFieldArchimedeanEnergy (numberFieldRankTwoCuspChart v hv A)
        (numberFieldVectorEmbedding
          (fun i => if i = (0 : Fin 2) then 1 else 0)) =
      numberFieldArchimedeanEnergy A (numberFieldVectorEmbedding v) := by
  let F := numberFieldRankTwoCuspFrame K v hv
  have hF : F.det = 1 := numberFieldRankTwoCuspFrame_det K v hv
  change numberFieldArchimedeanEnergy
      (numberFieldArchimedeanPositiveRationalConj F.transpose
        (by rw [Matrix.det_transpose, hF]) A)
      (numberFieldVectorEmbedding (fun i => if i = (0 : Fin 2) then 1 else 0)) = _
  rw [numberFieldArchimedeanEnergy_transposeRational F hF]
  congr 2
  have hb : (fun i : Fin 2 => if i = (0 : Fin 2) then (1 : K) else 0) =
      Pi.single (0 : Fin 2) 1 := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  rw [hb, Matrix.mulVec_single]
  funext i
  simp [F, numberFieldRankTwoCuspFrame_apply_zero]

end

end GaloisForLFunctions.HTGeometry

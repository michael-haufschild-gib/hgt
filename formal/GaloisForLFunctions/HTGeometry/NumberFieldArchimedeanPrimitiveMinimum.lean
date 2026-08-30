import GaloisForLFunctions.HTGeometry.ComplexHermitianRowRealification
import GaloisForLFunctions.HTGeometry.NumberFieldPositiveFormPrimitiveMinimum

/-!
# Primitive minima for the corrected archimedean cone

Every placewise real/Hermitian positive form over a number field determines one positive-definite
real matrix in canonical integral-basis coordinates.  Real places contribute their symmetric
blocks; complex places contribute faithful doubled-real Hermitian blocks.  The coordinate change,
positivity, and exact energy identity are all constructed here.

The resulting form attains its minimum on primitive number-ring vectors.  A minimizer extends to
the first column of a determinant-one integral matrix, with no retained form, Hilbert-space,
coordinate-equivalence, lattice, or compactness hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder Matrix NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Real local blocks followed by doubled-complex local blocks. -/
abbrev numberFieldArchimedeanBlockIndex (K : Type*) [Field K] (n : ℕ) :=
  ({w : InfinitePlace K // w.IsReal} × Fin n) ⊕
    ({w : InfinitePlace K // w.IsComplex} × (Fin n ⊕ Fin n))

/-- Identify block coordinates with the split place coordinates of number-field vectors. -/
def numberFieldArchimedeanBlockIndexEquiv (K : Type*) [Field K] (n : ℕ) :
    numberFieldArchimedeanBlockIndex K n ≃
      (Fin n × numberFieldMixedRealCoordinateIndex K) where
  toFun
    | Sum.inl (w, i) => (i, Sum.inl w)
    | Sum.inr (w, Sum.inl i) => (i, Sum.inr (w, 0))
    | Sum.inr (w, Sum.inr i) => (i, Sum.inr (w, 1))
  invFun p := match p.2 with
    | Sum.inl w => Sum.inl (w, p.1)
    | Sum.inr (w, j) =>
        if j = 0 then Sum.inr (w, Sum.inl p.1)
        else Sum.inr (w, Sum.inr p.1)
  left_inv x := by
    rcases x with ⟨w, i⟩ | ⟨w, i⟩
    · rfl
    · rcases i with i | i <;> simp
  right_inv p := by
    rcases p with ⟨i, w | ⟨w, j⟩⟩
    · rfl
    · fin_cases j <;> rfl

/-- Reindex a real coordinate function along an equivalence. -/
def realCoordinateReindex (e : α ≃ β) :
    (β → ℝ) ≃ₗ[ℝ] (α → ℝ) where
  toFun x a := x (e a)
  invFun y b := y (e.symm b)
  left_inv x := by funext b; simp
  right_inv y := by funext a; simp
  map_add' x y := rfl
  map_smul' c x := rfl

/-- Canonical integral-basis coordinates changed to real/Hermitian block coordinates. -/
def numberFieldCanonicalToArchimedeanBlockCoordinates (K : Type*)
    [Field K] [NumberField K] (n : ℕ) :
    (Fin (n * Module.finrank ℚ K) → ℝ) ≃ₗ[ℝ]
      (numberFieldArchimedeanBlockIndex K n → ℝ) :=
  (numberFieldCanonicalToPlaceCoordinates (K := K) n).trans
    (realCoordinateReindex (numberFieldArchimedeanBlockIndexEquiv K n))

/-- Matrix of the canonical-to-archimedean block coordinate equivalence. -/
def numberFieldArchimedeanCoordinateMatrix (K : Type*)
    [Field K] [NumberField K] (n : ℕ) :
    Matrix (numberFieldArchimedeanBlockIndex K n)
      (Fin (n * Module.finrank ℚ K)) ℝ :=
  LinearMap.toMatrix
    (Pi.basisFun ℝ (Fin (n * Module.finrank ℚ K)))
    (Pi.basisFun ℝ (numberFieldArchimedeanBlockIndex K n))
    (numberFieldCanonicalToArchimedeanBlockCoordinates K n).toLinearMap

/-- The coordinate matrix acts exactly as the underlying linear equivalence. -/
theorem numberFieldArchimedeanCoordinateMatrix_mulVec
    (x : Fin (n * Module.finrank ℚ K) → ℝ) :
    (numberFieldArchimedeanCoordinateMatrix K n).mulVec x =
      numberFieldCanonicalToArchimedeanBlockCoordinates K n x := by
  have h := LinearMap.toMatrix_mulVec_repr
      (Pi.basisFun ℝ (Fin (n * Module.finrank ℚ K)))
      (Pi.basisFun ℝ (numberFieldArchimedeanBlockIndex K n))
      (numberFieldCanonicalToArchimedeanBlockCoordinates K n).toLinearMap x
  change (numberFieldArchimedeanCoordinateMatrix K n).mulVec
      ((Pi.basisFun ℝ (Fin (n * Module.finrank ℚ K))).equivFun x) =
    (Pi.basisFun ℝ (numberFieldArchimedeanBlockIndex K n)).equivFun
      (numberFieldCanonicalToArchimedeanBlockCoordinates K n x) at h
  simpa [Pi.basisFun_equivFun] using h

/-- Orthogonal sum of every real block and every doubled-real Hermitian block. -/
def numberFieldArchimedeanBlockMatrix
    (A : numberFieldArchimedeanPositiveForms K n) :
    Matrix (numberFieldArchimedeanBlockIndex K n)
      (numberFieldArchimedeanBlockIndex K n) ℝ :=
  matrixOrthogonalSum
    (matrixFamilyBlockDiagonal (fun w =>
      (A.1.1 w : Matrix (Fin n) (Fin n) ℝ)))
    (matrixFamilyBlockDiagonal (fun w =>
      complexMatrixRowRealification
        (A.1.2 w : Matrix (Fin n) (Fin n) ℂ)))

/-- The assembled archimedean block matrix is positive definite. -/
theorem numberFieldArchimedeanBlockMatrix_posDef
    (A : numberFieldArchimedeanPositiveForms K n) :
    (numberFieldArchimedeanBlockMatrix A).PosDef := by
  apply matrixOrthogonalSum_posDef
  · exact matrixFamilyBlockDiagonal_posDef A.2.1
  · exact matrixFamilyBlockDiagonal_posDef fun w =>
      complexMatrixRowRealification_posDef (A.2.2 w)

/-- Pull the archimedean block form back to canonical integral-basis coordinates. -/
def numberFieldArchimedeanCanonicalMatrix
    (A : numberFieldArchimedeanPositiveForms K n) :
    Matrix (Fin (n * Module.finrank ℚ K))
      (Fin (n * Module.finrank ℚ K)) ℝ :=
  let P := numberFieldArchimedeanCoordinateMatrix K n
  Pᴴ * numberFieldArchimedeanBlockMatrix A * P

/-- The canonical real archimedean matrix is positive definite. -/
theorem numberFieldArchimedeanCanonicalMatrix_posDef
    (A : numberFieldArchimedeanPositiveForms K n) :
    (numberFieldArchimedeanCanonicalMatrix A).PosDef := by
  apply (numberFieldArchimedeanBlockMatrix_posDef A).conjTranspose_mul_mul_same
  intro x y hxy
  apply (numberFieldCanonicalToArchimedeanBlockCoordinates K n).injective
  rw [← numberFieldArchimedeanCoordinateMatrix_mulVec,
    ← numberFieldArchimedeanCoordinateMatrix_mulVec, hxy]

/-- Real block coordinates of a mixed vector are its real-place coordinates. -/
theorem numberFieldCanonicalToArchimedeanBlockCoordinates_real
    (z : Fin n → mixedEmbedding.mixedSpace K)
    (w : {w : InfinitePlace K // w.IsReal}) (i : Fin n) :
    numberFieldCanonicalToArchimedeanBlockCoordinates K n
        (numberFieldMixedVectorContinuousLinearEquiv K n z)
      (Sum.inl (w, i)) =
      (z i).1 w := by
  simp [numberFieldCanonicalToArchimedeanBlockCoordinates,
    realCoordinateReindex, numberFieldArchimedeanBlockIndexEquiv,
    numberFieldCanonicalToPlaceCoordinates_apply,
    numberFieldMixedVectorPlaceCoordinates, numberFieldMixedRealCoordinates]

/-- First doubled coordinate of a complex place is its real part. -/
theorem numberFieldCanonicalToArchimedeanBlockCoordinates_complex_re
    (z : Fin n → mixedEmbedding.mixedSpace K)
    (w : {w : InfinitePlace K // w.IsComplex}) (i : Fin n) :
    numberFieldCanonicalToArchimedeanBlockCoordinates K n
        (numberFieldMixedVectorContinuousLinearEquiv K n z)
        (Sum.inr (w, Sum.inl i)) =
      ((z i).2 w).re := by
  simp [numberFieldCanonicalToArchimedeanBlockCoordinates,
    realCoordinateReindex, numberFieldArchimedeanBlockIndexEquiv,
    numberFieldCanonicalToPlaceCoordinates_apply,
    numberFieldMixedVectorPlaceCoordinates, numberFieldMixedRealCoordinates]

/-- Second doubled coordinate of a complex place is its imaginary part. -/
theorem numberFieldCanonicalToArchimedeanBlockCoordinates_complex_im
    (z : Fin n → mixedEmbedding.mixedSpace K)
    (w : {w : InfinitePlace K // w.IsComplex}) (i : Fin n) :
    numberFieldCanonicalToArchimedeanBlockCoordinates K n
        (numberFieldMixedVectorContinuousLinearEquiv K n z)
        (Sum.inr (w, Sum.inr i)) =
      ((z i).2 w).im := by
  simp [numberFieldCanonicalToArchimedeanBlockCoordinates,
    realCoordinateReindex, numberFieldArchimedeanBlockIndexEquiv,
    numberFieldCanonicalToPlaceCoordinates_apply,
    numberFieldMixedVectorPlaceCoordinates, numberFieldMixedRealCoordinates]

/-- Sum of the real and Hermitian quadratic energies at all infinite places. -/
def numberFieldArchimedeanEnergy
    (A : numberFieldArchimedeanPositiveForms K n)
    (z : Fin n → mixedEmbedding.mixedSpace K) : ℝ :=
  (∑ w : {w : InfinitePlace K // w.IsReal},
    (fun i => (z i).1 w) ⬝ᵥ
      (A.1.1 w : Matrix (Fin n) (Fin n) ℝ).mulVec
        (fun i => (z i).1 w)) +
  ∑ w : {w : InfinitePlace K // w.IsComplex},
    (((fun i => (z i).2 w) ⬝ᵥ
      (A.1.2 w : Matrix (Fin n) (Fin n) ℂ).mulVec
        (star (fun i => (z i).2 w))).re)

/-- The block matrix has exactly the intended placewise archimedean energy. -/
theorem numberFieldArchimedeanBlockMatrix_quadratic
    (A : numberFieldArchimedeanPositiveForms K n)
    (z : Fin n → mixedEmbedding.mixedSpace K) :
    let x := numberFieldCanonicalToArchimedeanBlockCoordinates K n
      (numberFieldMixedVectorContinuousLinearEquiv K n z)
    x ⬝ᵥ (numberFieldArchimedeanBlockMatrix A).mulVec x =
      numberFieldArchimedeanEnergy A z := by
  dsimp only
  rw [numberFieldArchimedeanBlockMatrix, matrixOrthogonalSum_quadratic,
    matrixFamilyBlockDiagonal_quadratic, matrixFamilyBlockDiagonal_quadratic]
  unfold numberFieldArchimedeanEnergy
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    have hx : (fun i =>
        numberFieldCanonicalToArchimedeanBlockCoordinates K n
          (numberFieldMixedVectorContinuousLinearEquiv K n z)
          (Sum.inl (w, i))) = fun i => (z i).1 w := by
      funext i
      exact numberFieldCanonicalToArchimedeanBlockCoordinates_real z w i
    rw [hx]
  · apply Finset.sum_congr rfl
    intro w hw
    rw [complexMatrixRowRealification_quadratic]
    have hx : complexOfDoubledReal (fun i =>
        numberFieldCanonicalToArchimedeanBlockCoordinates K n
          (numberFieldMixedVectorContinuousLinearEquiv K n z)
          (Sum.inr (w, i))) = fun i => (z i).2 w := by
      funext i
      apply Complex.ext
      · exact numberFieldCanonicalToArchimedeanBlockCoordinates_complex_re z w i
      · exact numberFieldCanonicalToArchimedeanBlockCoordinates_complex_im z w i
    rw [hx]

/-- Canonical-coordinate quadratic evaluation is exact archimedean energy. -/
theorem numberFieldArchimedeanCanonicalMatrix_quadratic
    (A : numberFieldArchimedeanPositiveForms K n)
    (z : Fin n → mixedEmbedding.mixedSpace K) :
    let c := numberFieldMixedVectorContinuousLinearEquiv K n z
    c ⬝ᵥ (numberFieldArchimedeanCanonicalMatrix A).mulVec c =
      numberFieldArchimedeanEnergy A z := by
  dsimp only
  rw [numberFieldArchimedeanCanonicalMatrix]
  calc
    _ = (numberFieldArchimedeanCoordinateMatrix K n).mulVec
          (numberFieldMixedVectorContinuousLinearEquiv K n z) ⬝ᵥ
        (numberFieldArchimedeanBlockMatrix A).mulVec
          ((numberFieldArchimedeanCoordinateMatrix K n).mulVec
            (numberFieldMixedVectorContinuousLinearEquiv K n z)) := by
      simpa only [star_trivial] using
        (star_dotProduct_real_congr_mulVec
          (numberFieldArchimedeanBlockMatrix A)
          (numberFieldArchimedeanCoordinateMatrix K n)
          (numberFieldMixedVectorContinuousLinearEquiv K n z))
    _ = _ := by
      rw [numberFieldArchimedeanCoordinateMatrix_mulVec]
      exact numberFieldArchimedeanBlockMatrix_quadratic A z

/-- A corrected real/Hermitian archimedean form attains its primitive number-ring minimum, and a
minimizer extends to the first column of a determinant-one integral matrix. -/
theorem exists_numberFieldArchimedean_minimalPrimitiveVector
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 2 ≤ n)
    (A : numberFieldArchimedeanPositiveForms K n) :
    ∃ (a : Fin n → 𝓞 K) (β : Matrix (Fin n) (Fin n) (𝓞 K)),
      (∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1) ∧
      (∀ b : Fin n → 𝓞 K,
        (∃ p : Fin n → 𝓞 K, ∑ i, p i * b i = 1) →
        numberFieldArchimedeanEnergy A
            (numberFieldIntegerVectorEmbedding K a) ≤
          numberFieldArchimedeanEnergy A
            (numberFieldIntegerVectorEmbedding K b)) ∧
      β.det = 1 ∧
      ∀ i, β i ⟨0, lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ = a i := by
  obtain ⟨a, β, hprim, hmin, hdet, hcol⟩ :=
    exists_numberFieldInteger_minimalPrimitiveVector_posDef K n hn
      (numberFieldArchimedeanCanonicalMatrix A)
      (numberFieldArchimedeanCanonicalMatrix_posDef A)
  refine ⟨a, β, hprim, ?_, hdet, hcol⟩
  intro b hb
  have h := hmin b hb
  dsimp only at h
  simpa only [numberFieldArchimedeanCanonicalMatrix_quadratic] using h

end

end GaloisForLFunctions.HTGeometry

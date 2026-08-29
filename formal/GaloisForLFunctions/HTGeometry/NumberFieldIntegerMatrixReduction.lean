import GaloisForLFunctions.HTGeometry.NumberFieldIntegerBasis

/-!
# Integral matrix size reduction at all infinite places

The canonical mixed embedding gives a uniform covering radius for `𝓞 K`.  Applying the same radius
entrywise produces an integral matrix approximation.  Restricting the chosen entries to the strict
upper triangle produces an actual upper-unitriangular matrix of determinant one.  Thus neither the
integral matrix, its unimodularity, nor a place-by-place approximation hypothesis remains external.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

/-- One field-dependent radius approximates every finite matrix of mixed-embedding vectors by a
matrix of actual algebraic integers. -/
theorem exists_numberFieldInteger_matrixCoveringRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)),
        ∃ a : Matrix (Fin n) (Fin n) (𝓞 K),
          ∀ i j, ‖x i j - mixedEmbedding K (a i j : K)‖ ≤ R := by
  rcases exists_numberFieldInteger_coveringRadius K with ⟨R, hR, hcover⟩
  refine ⟨R, hR, ?_⟩
  intro n x
  choose a ha using fun i j ↦ hcover (x i j)
  exact ⟨a, ha⟩

/-- Uniform strict-upper size reduction over `𝓞 K`.  The produced matrix is not merely integral:
it is upper unitriangular and has determinant exactly one. -/
theorem exists_numberFieldInteger_unipotentUpperReduction
    (K : Type*) [Field K] [NumberField K] :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)),
        ∃ U : Matrix (Fin n) (Fin n) (𝓞 K),
          (∀ i, U i i = 1) ∧
          (∀ i j, j < i → U i j = 0) ∧
          (∀ i j, i < j → ‖x i j - mixedEmbedding K (U i j : K)‖ ≤ R) ∧
          U.det = 1 := by
  rcases exists_numberFieldInteger_coveringRadius K with ⟨R, hR, hcover⟩
  refine ⟨R, hR, ?_⟩
  intro n x
  choose a ha using fun i j ↦ hcover (x i j)
  let U : Matrix (Fin n) (Fin n) (𝓞 K) := fun i j ↦
    if i = j then 1 else if i < j then a i j else 0
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [U]
  · intro i j hji
    simp [U, ne_of_gt hji, hji.asymm]
  · intro i j hij
    simpa [U, ne_of_lt hij, hij] using ha i j
  · rw [Matrix.det_of_upperTriangular]
    · simp [U]
    · intro i j hji
      change j < i at hji
      simp [U, ne_of_gt hji, hji.asymm]

end

end GaloisForLFunctions.HTGeometry

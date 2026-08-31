import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanFirstGreedy
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanSchurAction

/-!
# Recursive primitive-minimal archimedean flags

Successive primitive minima are chosen inside the proof.  Each lower-rank normalization is lifted
through the first Schur tail, and the resulting determinant-one matrices are assembled into one
full-rank integral action.  No basis, lattice, minimizer, completion, or Schur witness is a premise.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder Matrix NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Bezout formulation of primitivity for a number-ring coordinate vector. -/
def NumberFieldIntegerVector.IsPrimitive (b : Fin n → 𝓞 K) : Prop :=
  ∃ p : Fin n → 𝓞 K, ∑ i, p i * b i = 1

omit [NumberField K] in
/-- Determinant-one integral matrices preserve primitive coordinate vectors. -/
theorem NumberFieldIntegerVector.IsPrimitive.detOne_mulVec
    {b : Fin n → 𝓞 K} (hb : NumberFieldIntegerVector.IsPrimitive b)
    (B : Matrix (Fin n) (Fin n) (𝓞 K)) (hB : B.det = 1) :
    NumberFieldIntegerVector.IsPrimitive (B.mulVec b) := by
  obtain ⟨p, hp⟩ := hb
  have hunit : IsUnit B.det := by rw [hB]; exact isUnit_one
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hunit
  refine ⟨Matrix.vecMul p B⁻¹, ?_⟩
  change dotProduct (Matrix.vecMul p B⁻¹) (B.mulVec b) = 1
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hinv]
  simpa [dotProduct] using hp

omit [NumberField K] in
/-- The transposed head-fixed lift fixes the first standard coordinate. -/
theorem transpose_matrixFirstTailLift_mulVec_firstCoordinate
    (B : Matrix (Fin n) (Fin n) (𝓞 K)) :
    (matrixFirstTailLift B).transpose.mulVec
        (numberFieldCoordinateBasis (K := K) (0 : Fin (n + 1))) =
      numberFieldCoordinateBasis (K := K) (0 : Fin (n + 1)) := by
  rw [mulVec_numberFieldCoordinateBasis]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [numberFieldCoordinateBasis]
  · simp [numberFieldCoordinateBasis]

omit [NumberField K] in
/-- Explicit positive-cone congruence respects multiplication. -/
theorem numberFieldArchimedeanPositiveConj_mul
    (g h : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (A : numberFieldArchimedeanPositiveForms K n) :
    numberFieldArchimedeanPositiveConj (g * h) A =
      numberFieldArchimedeanPositiveConj g
        (numberFieldArchimedeanPositiveConj h A) := by
  apply Subtype.ext
  exact numberFieldArchimedeanConj_mul g h A.1

/-- A recursively greedy point: every nonterminal Schur head is globally minimal among primitive
number-ring vectors, then the same condition holds on its first Schur tail. -/
def NumberFieldArchimedeanGreedyFlag :
    (m : ℕ) → numberFieldArchimedeanPositiveForms K m → Prop
  | 0, _ => True
  | 1, _ => True
  | m + 2, A =>
      (∀ b : Fin (m + 2) → 𝓞 K,
          NumberFieldIntegerVector.IsPrimitive b →
          numberFieldArchimedeanEnergy A
              (numberFieldIntegerVectorEmbedding K
                (numberFieldCoordinateBasis (K := K) (0 : Fin (m + 2)))) ≤
            numberFieldArchimedeanEnergy A
              (numberFieldIntegerVectorEmbedding K b)) ∧
        NumberFieldArchimedeanGreedyFlag (m + 1)
          (numberFieldArchimedeanSchur A)

/-- Every corrected archimedean cone point admits one internally constructed determinant-one
integral action whose complete Schur flag is recursively primitive-minimal. -/
theorem exists_numberFieldArchimedean_greedyFlag
    (K : Type*) [Field K] [NumberField K] :
    ∀ (m : ℕ) (A : numberFieldArchimedeanPositiveForms K m),
      ∃ (B : Matrix (Fin m) (Fin m) (𝓞 K)) (hB : B.det = 1),
        NumberFieldArchimedeanGreedyFlag m
          (numberFieldArchimedeanPositiveConj
            (transposeSpecialLinearOfDetOne B hB) A) := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero =>
      intro A
      refine ⟨1, Matrix.det_one, ?_⟩
      trivial
  | one =>
      intro A
      refine ⟨1, Matrix.det_one, ?_⟩
      trivial
  | more m ih0 ih1 =>
      intro A
      obtain ⟨a, B₀, ha, hmin, hB₀, hcol⟩ :=
        exists_numberFieldArchimedean_minimalPrimitiveVector K (m + 2)
          (by omega) A
      let G₀ : Matrix.SpecialLinearGroup (Fin (m + 2)) (𝓞 K) :=
        transposeSpecialLinearOfDetOne B₀ hB₀
      let A₀ : numberFieldArchimedeanPositiveForms K (m + 2) :=
        numberFieldArchimedeanPositiveConj G₀ A
      obtain ⟨B₁, hB₁, hflag₁⟩ := ih1 (numberFieldArchimedeanSchur A₀)
      let G₁ : Matrix.SpecialLinearGroup (Fin (m + 1)) (𝓞 K) :=
        transposeSpecialLinearOfDetOne B₁ hB₁
      let T : Matrix (Fin (m + 2)) (Fin (m + 2)) (𝓞 K) :=
        specialLinearFirstTailLift G₁
      let B : Matrix (Fin (m + 2)) (Fin (m + 2)) (𝓞 K) := B₀ * T.transpose
      have hT : T.det = 1 := by
        exact Matrix.SpecialLinearGroup.det_coe (specialLinearFirstTailLift G₁)
      have hB : B.det = 1 := by
        dsimp only [B]
        rw [Matrix.det_mul, Matrix.det_transpose, hB₀, hT, one_mul]
      refine ⟨B, hB, ?_⟩
      have hG : transposeSpecialLinearOfDetOne B hB =
          specialLinearFirstTailLift G₁ * G₀ := by
        apply Subtype.ext
        simp [transposeSpecialLinearOfDetOne, B, T, Matrix.transpose_mul, G₀]
      have hA : numberFieldArchimedeanPositiveConj
            (transposeSpecialLinearOfDetOne B hB) A =
          numberFieldArchimedeanPositiveConj (specialLinearFirstTailLift G₁) A₀ := by
        rw [hG, numberFieldArchimedeanPositiveConj_mul]
      change (∀ b : Fin (m + 2) → 𝓞 K,
          NumberFieldIntegerVector.IsPrimitive b →
          numberFieldArchimedeanEnergy
              (numberFieldArchimedeanPositiveConj
                (transposeSpecialLinearOfDetOne B hB) A)
              (numberFieldIntegerVectorEmbedding K
                (numberFieldCoordinateBasis (K := K) (0 : Fin (m + 2)))) ≤
            numberFieldArchimedeanEnergy
              (numberFieldArchimedeanPositiveConj
                (transposeSpecialLinearOfDetOne B hB) A)
              (numberFieldIntegerVectorEmbedding K b)) ∧ _
      constructor
      · intro b hb
        change numberFieldArchimedeanEnergy
              ((transposeSpecialLinearOfDetOne B hB) • A)
              (numberFieldIntegerVectorEmbedding K
                (numberFieldCoordinateBasis (K := K) (0 : Fin (m + 2)))) ≤
            numberFieldArchimedeanEnergy
              ((transposeSpecialLinearOfDetOne B hB) • A)
              (numberFieldIntegerVectorEmbedding K b)
        rw [numberFieldArchimedeanEnergy_transposeSpecialLinear,
          numberFieldArchimedeanEnergy_transposeSpecialLinear]
        have hfirst : B.mulVec
              (numberFieldCoordinateBasis (K := K) (0 : Fin (m + 2))) = a := by
          dsimp only [B]
          rw [← Matrix.mulVec_mulVec]
          dsimp only [T, specialLinearFirstTailLift]
          rw [transpose_matrixFirstTailLift_mulVec_firstCoordinate]
          rw [mulVec_numberFieldCoordinateBasis]
          funext i
          exact hcol i
        rw [hfirst]
        exact hmin _ (hb.detOne_mulVec B hB)
      · rw [hA,
          numberFieldArchimedeanSchur_specialLinearFirstTailLift]
        exact hflag₁

end

end GaloisForLFunctions.HTGeometry

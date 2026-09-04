import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanDetRootShortVector
import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoFiniteCuspRepresentatives

/-!
# Determinant-root short vectors classified by finite cusps

In rank two, the determinant-normalized Minkowski vector is classified immediately by the finite
projective `SL₂(𝒪_K)` cusp family.  The energy bound and projective map are returned by one
unconditional theorem, retaining the exact canonical determinant scale.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField Module
open scoped Classical NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- An integral rank-two vector viewed as a nonzero vector over the number field. -/
def numberFieldRankTwoNonzeroVectorOfInteger
    (a : Fin 2 → RingOfIntegers K) (ha : a ≠ 0) :
    numberFieldRankTwoNonzeroVector K :=
  ⟨fun i ↦ (a i : K), by
    intro h
    apply ha
    funext i
    apply Subtype.ext
    have hi := congrFun h i
    change (a i : K) = 0 at hi
    exact hi⟩

/-- Rank-two determinant-root Minkowski reduction lands in one of the fixed finite cusp orbits. -/
theorem exists_uniform_numberFieldArchimedean_finiteCuspShortVector :
    ∃ R : ℝ, 0 < R ∧
      ∀ A : numberFieldArchimedeanPositiveForms K 2,
        ∃ (a : Fin 2 → RingOfIntegers K), a ≠ 0 ∧
          numberFieldArchimedeanEnergy A
              (numberFieldIntegerVectorEmbedding K a) ≤
            ((2 * Module.finrank ℚ K : ℕ) : ℝ) * R ^ 2 *
              Real.rpow (numberFieldArchimedeanCanonicalMatrix A).det
                (((2 * Module.finrank ℚ K : ℕ) : ℝ)⁻¹) ∧
          ∃ c : numberFieldRankTwoCuspType K,
            ∃ g : Matrix.SpecialLinearGroup (Fin 2) (RingOfIntegers K),
              ∃ scalar : K, scalar ≠ 0 ∧ ∀ i,
                (numberFieldRankTwoMatrixBaseChange K
                  (g : Matrix (Fin 2) (Fin 2) (RingOfIntegers K))).mulVec
                    (fun j ↦ (a j : K)) i =
                  scalar * (numberFieldRankTwoCuspRepresentative K c).1 i := by
  obtain ⟨R, hR, hbound⟩ :=
    exists_uniform_numberFieldArchimedeanEnergy_le_canonicalDetRoot K 2 (by omega)
  refine ⟨R, hR, ?_⟩
  intro A
  obtain ⟨a, ha0, ha⟩ := hbound A
  obtain ⟨c, g, scalar, hscalar, hmap⟩ :=
    exists_numberFieldRankTwo_finiteCuspRepresentative_projectiveMap K
      (numberFieldRankTwoNonzeroVectorOfInteger K a ha0)
  exact ⟨a, ha0, ha, c, g, scalar, hscalar, hmap⟩

end

end GaloisForLFunctions.HTGeometry

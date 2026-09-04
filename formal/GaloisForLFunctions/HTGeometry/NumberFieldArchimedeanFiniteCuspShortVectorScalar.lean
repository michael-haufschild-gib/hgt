import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanFiniteCuspShortVector
import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoCuspScalarProduct

/-!
# Product-normalized finite-cusp short vectors

Rank-two determinant-root Minkowski reduction and finite projective cusp classification are
combined with the algebraic-integer product formula.  The returned projective scalar has a
weighted logarithmic lower bound depending only on its chosen finite cusp representative.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField Module
open scoped Classical NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Rank-two determinant-root reduction returns a finite cusp and a projective scalar whose
weighted archimedean logarithm has the exact product-formula lower bound. -/
theorem exists_uniform_numberFieldArchimedean_finiteCuspShortVector_scalarProduct :
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
              ∃ scalar : K, scalar ≠ 0 ∧
                (∀ i, (numberFieldRankTwoMatrixBaseChange K
                  (g : Matrix (Fin 2) (Fin 2) (RingOfIntegers K))).mulVec
                    (fun j ↦ (a j : K)) i =
                  scalar * (numberFieldRankTwoCuspRepresentative K c).1 i) ∧
                -numberFieldWeightedPlaceMean (fun w ↦ Real.log
                    (w ((numberFieldRankTwoCuspRepresentative K c).1
                      (numberFieldRankTwoCuspRepresentativeIndex c)))) ≤
                  numberFieldWeightedPlaceMean
                    (fun w ↦ Real.log (w scalar)) := by
  obtain ⟨R, hR, hshort⟩ :=
    exists_uniform_numberFieldArchimedean_finiteCuspShortVector K
  refine ⟨R, hR, ?_⟩
  intro A
  obtain ⟨a, ha, henergy, c, g, scalar, hscalar, hmap⟩ := hshort A
  refine ⟨a, ha, henergy, c, g, scalar, hscalar, hmap, ?_⟩
  exact numberFieldRankTwo_projectiveCuspScalar_weightedMean_lower
    a c g scalar hscalar hmap

end

end GaloisForLFunctions.HTGeometry

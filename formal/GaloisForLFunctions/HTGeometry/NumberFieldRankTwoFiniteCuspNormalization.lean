import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoCuspInvariant

/-!
# Finite cusp normalization for rank-two number-field vectors

Every nonzero rank-two vector is projectively rescaled into the slice whose coordinate ideal is the
fixed representative of its ideal class.  The indexing class group is finite, so this gives the
literal finite-cusp decomposition needed by number-field reduction theory.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Steinitz normalization preserves nonvanishing of a rank-two vector. -/
theorem numberFieldRankTwoNormalizedVector_ne_zero
    (v : Fin 2 → K) (hv : v ≠ 0) :
    numberFieldRankTwoNormalizedVector K v hv ≠ 0 := by
  intro hzero
  apply hv
  funext i
  rw [← numberFieldRankTwo_normalizer_mul_normalizedVector K v hv i]
  simp [hzero]

/-- Steinitz normalization as a map on nonzero rank-two vectors. -/
def numberFieldRankTwoNormalizedNonzeroVector
    (v : numberFieldRankTwoNonzeroVector K) :
    numberFieldRankTwoNonzeroVector K :=
  ⟨numberFieldRankTwoNormalizedVector K v.1 v.2,
    numberFieldRankTwoNormalizedVector_ne_zero K v.1 v.2⟩

/-- Projective vectors whose coordinate ideal is the fixed representative of `c`. -/
def numberFieldRankTwoCuspSlice (c : ClassGroup (𝓞 K)) :
    Set (numberFieldRankTwoNonzeroVector K) :=
  {v | numberFieldRankTwoCoordinateIdeal K v.1 =
    (numberFieldIdealClassRepresentative K c :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K)}

/-- The normalized vector belongs to the slice indexed by its original cusp class. -/
theorem numberFieldRankTwoNormalizedNonzeroVector_mem_cuspSlice
    (v : numberFieldRankTwoNonzeroVector K) :
    numberFieldRankTwoNormalizedNonzeroVector K v ∈
      numberFieldRankTwoCuspSlice K (numberFieldRankTwoCuspClass K v) := by
  exact numberFieldRankTwoNormalizedVector_coordinateIdeal K v.1 v.2

/-- Projective Steinitz normalization does not change the cusp ideal class. -/
theorem numberFieldRankTwoCuspClass_normalized
    (v : numberFieldRankTwoNonzeroVector K) :
    numberFieldRankTwoCuspClass K
        (numberFieldRankTwoNormalizedNonzeroVector K v) =
      numberFieldRankTwoCuspClass K v := by
  unfold numberFieldRankTwoCuspClass numberFieldRankTwoNormalizedNonzeroVector
    numberFieldRankTwoCoordinateIdealUnit
  have hcoord := numberFieldRankTwoNormalizedVector_coordinateIdeal K v.1 v.2
  have hunit :
      Units.mk0
          (numberFieldRankTwoCoordinateIdeal K
            (numberFieldRankTwoNormalizedVector K v.1 v.2))
          (numberFieldRankTwoCoordinateIdeal_ne_zero K
            (numberFieldRankTwoNormalizedVector_ne_zero K v.1 v.2)) =
        numberFieldIdealClassRepresentative K
          (ClassGroup.mk K (numberFieldRankTwoCoordinateIdealUnit K v.1 v.2)) := by
    apply Units.ext
    exact hcoord
  rw [hunit, numberFieldIdealClassRepresentative_mk]
  congr 1

/-- **Finite-cusp projective normalization.**  Every nonzero vector is a nonzero scalar multiple
of a vector in one of the fixed ideal-class slices. -/
theorem exists_numberFieldRankTwo_finiteCuspNormalization
    (v : numberFieldRankTwoNonzeroVector K) :
    ∃ c : ClassGroup (𝓞 K),
      ∃ w ∈ numberFieldRankTwoCuspSlice K c,
      ∃ a : K, a ≠ 0 ∧ ∀ i,
        a * w.1 i = v.1 i := by
  let c := numberFieldRankTwoCuspClass K v
  let w := numberFieldRankTwoNormalizedNonzeroVector K v
  let a := numberFieldIdealClassNormalizer K
    (numberFieldRankTwoCoordinateIdealUnit K v.1 v.2)
  exact ⟨c, w,
    numberFieldRankTwoNormalizedNonzeroVector_mem_cuspSlice K v,
    a, numberFieldIdealClassNormalizer_ne_zero K _,
    numberFieldRankTwo_normalizer_mul_normalizedVector K v.1 v.2⟩

end

end GaloisForLFunctions.HTGeometry

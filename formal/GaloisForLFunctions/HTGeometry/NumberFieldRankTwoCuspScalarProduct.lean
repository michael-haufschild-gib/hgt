import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoFiniteCuspRepresentatives
import GaloisForLFunctions.HTGeometry.NumberFieldBoundedPrincipalIdeals
import GaloisForLFunctions.HTGeometry.NumberFieldDetOneUnitWeightBalancing

/-!
# Product-formula control of rank-two cusp scalars

An integral vector transported projectively to a fixed cusp representative has one coordinate of
the form `scalar * representativeCoordinate` that is a nonzero algebraic integer.  The number-field
product formula therefore prevents the projective scalar from collapsing at all archimedean places.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- A nonzero integral product controls the weighted archimedean size of its first factor by that
of its second factor. -/
theorem neg_numberFieldWeightedPlaceMean_log_le_of_integer_eq_mul
    (z : 𝓞 K) (hz : z ≠ 0) (a c : K) (ha : a ≠ 0) (hc : c ≠ 0)
    (hzc : (z : K) = a * c) :
    -numberFieldWeightedPlaceMean (fun w ↦ Real.log (w c)) ≤
      numberFieldWeightedPlaceMean (fun w ↦ Real.log (w a)) := by
  have hsum := weightedSum_numberFieldIntegerPlaceLog_nonneg z hz
  have hsplit :
      (∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w (z : K))) =
        (∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w a)) +
          ∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w c) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    rw [hzc, map_mul, Real.log_mul]
    · ring
    · exact ne_of_gt (by rw [InfinitePlace.pos_iff]; exact ha)
    · exact ne_of_gt (by rw [InfinitePlace.pos_iff]; exact hc)
  rw [hsplit] at hsum
  have hweight : 0 < numberFieldInfinitePlaceWeight (K := K) :=
    numberFieldInfinitePlaceWeight_pos (K := K)
  unfold numberFieldWeightedPlaceMean
  rw [show -((∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w c)) /
      numberFieldInfinitePlaceWeight (K := K)) =
    (-∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w c)) /
      numberFieldInfinitePlaceWeight (K := K) by ring]
  apply (div_le_div_iff_of_pos_right hweight).2
  linarith

/-- Every chosen finite-cusp representative has a selected nonzero coordinate. -/
def numberFieldRankTwoCuspRepresentativeIndex
    (c : numberFieldRankTwoCuspType K) : Fin 2 :=
  Classical.choose (Function.ne_iff.mp
    (numberFieldRankTwoCuspRepresentative K c).2)

theorem numberFieldRankTwoCuspRepresentativeIndex_ne_zero
    (c : numberFieldRankTwoCuspType K) :
    (numberFieldRankTwoCuspRepresentative K c).1
      (numberFieldRankTwoCuspRepresentativeIndex c) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp
    (numberFieldRankTwoCuspRepresentative K c).2)

omit [NumberField K] in
/-- Scalar extension of an integral matrix-vector product is the corresponding number-field
matrix-vector product. -/
theorem numberFieldRankTwoMatrixBaseChange_mulVec_integer
    (g : Matrix (Fin 2) (Fin 2) (𝓞 K)) (v : Fin 2 → 𝓞 K) (i : Fin 2) :
    ((g.mulVec v i : 𝓞 K) : K) =
      (numberFieldRankTwoMatrixBaseChange K g).mulVec
        (fun j ↦ (v j : K)) i := by
  simp [Matrix.mulVec, dotProduct, numberFieldRankTwoMatrixBaseChange]

/-- In a projective integral cusp transport, the scalar times the selected representative
coordinate is a literal nonzero algebraic integer. -/
theorem exists_numberFieldInteger_eq_projectiveCuspScalar_mul_selectedCoordinate
    (v : Fin 2 → 𝓞 K)
    (c : numberFieldRankTwoCuspType K)
    (g : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K))
    (a : K) (ha : a ≠ 0)
    (hmap : ∀ i, (numberFieldRankTwoMatrixBaseChange K
      (g : Matrix (Fin 2) (Fin 2) (𝓞 K))).mulVec
        (fun j ↦ (v j : K)) i =
          a * (numberFieldRankTwoCuspRepresentative K c).1 i) :
    ∃ z : 𝓞 K, z ≠ 0 ∧
      (z : K) = a * (numberFieldRankTwoCuspRepresentative K c).1
        (numberFieldRankTwoCuspRepresentativeIndex c) := by
  let i := numberFieldRankTwoCuspRepresentativeIndex c
  let z : 𝓞 K :=
    (g : Matrix (Fin 2) (Fin 2) (𝓞 K)).mulVec v i
  have hzcast : (z : K) =
      a * (numberFieldRankTwoCuspRepresentative K c).1 i := by
    rw [numberFieldRankTwoMatrixBaseChange_mulVec_integer]
    exact hmap i
  have hz : z ≠ 0 := by
    intro hz0
    have hcast0 : (z : K) = 0 := by rw [hz0]; rfl
    rw [hzcast] at hcast0
    exact mul_ne_zero ha
      (numberFieldRankTwoCuspRepresentativeIndex_ne_zero c) hcast0
  exact ⟨z, hz, hzcast⟩

/-- The projective scalar in an integral transport to a chosen cusp has a weighted logarithmic
lower bound depending only on that fixed cusp representative. -/
theorem numberFieldRankTwo_projectiveCuspScalar_weightedMean_lower
    (v : Fin 2 → 𝓞 K)
    (c : numberFieldRankTwoCuspType K)
    (g : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K))
    (a : K) (ha : a ≠ 0)
    (hmap : ∀ i, (numberFieldRankTwoMatrixBaseChange K
      (g : Matrix (Fin 2) (Fin 2) (𝓞 K))).mulVec
        (fun j ↦ (v j : K)) i =
          a * (numberFieldRankTwoCuspRepresentative K c).1 i) :
    -numberFieldWeightedPlaceMean (fun w ↦ Real.log
        (w ((numberFieldRankTwoCuspRepresentative K c).1
          (numberFieldRankTwoCuspRepresentativeIndex c)))) ≤
      numberFieldWeightedPlaceMean (fun w ↦ Real.log (w a)) := by
  obtain ⟨z, hz, hza⟩ :=
    exists_numberFieldInteger_eq_projectiveCuspScalar_mul_selectedCoordinate
      v c g a ha hmap
  exact neg_numberFieldWeightedPlaceMean_log_le_of_integer_eq_mul
    z hz a
      ((numberFieldRankTwoCuspRepresentative K c).1
        (numberFieldRankTwoCuspRepresentativeIndex c))
      ha (numberFieldRankTwoCuspRepresentativeIndex_ne_zero c) hza

/-- Every nonzero integral rank-two vector admits a finite-cusp transport whose projective scalar
has the uniform product-formula lower bound attached to the chosen representative. -/
theorem exists_numberFieldRankTwo_finiteCuspRepresentative_scalar_weightedMean_lower
    (K : Type*) [Field K] [NumberField K]
    (v : Fin 2 → 𝓞 K) (hv : v ≠ 0) :
    ∃ c : numberFieldRankTwoCuspType K,
      ∃ g : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K),
        ∃ a : K, a ≠ 0 ∧
          (∀ i, (numberFieldRankTwoMatrixBaseChange K
            (g : Matrix (Fin 2) (Fin 2) (𝓞 K))).mulVec
              (fun j ↦ (v j : K)) i =
                a * (numberFieldRankTwoCuspRepresentative K c).1 i) ∧
          -numberFieldWeightedPlaceMean (fun w ↦ Real.log
              (w ((numberFieldRankTwoCuspRepresentative K c).1
                (numberFieldRankTwoCuspRepresentativeIndex c)))) ≤
            numberFieldWeightedPlaceMean (fun w ↦ Real.log (w a)) := by
  let vK : numberFieldRankTwoNonzeroVector K :=
    ⟨fun i ↦ (v i : K), by
      intro hzero
      apply hv
      funext i
      apply Subtype.ext
      exact congrFun hzero i⟩
  obtain ⟨c, g, a, ha, hmap⟩ :=
    exists_numberFieldRankTwo_finiteCuspRepresentative_projectiveMap K vK
  refine ⟨c, g, a, ha, hmap, ?_⟩
  exact numberFieldRankTwo_projectiveCuspScalar_weightedMean_lower
    v c g a ha hmap

end

end GaloisForLFunctions.HTGeometry

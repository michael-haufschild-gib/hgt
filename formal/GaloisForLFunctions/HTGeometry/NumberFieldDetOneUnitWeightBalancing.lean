import GaloisForLFunctions.HTGeometry.NumberFieldDetOneUnitDiagonal

/-!
# Unconditional determinant-one unit balancing of place weights

Double centering separates arbitrary logarithmic weights into a coordinate mean, a place mean, and
a residual lying in the weighted-zero unit-log hyperplane in each coordinate and summing to zero
across coordinates.  Determinant-one unit covering uniformly absorbs that residual.  No selected
units, log-lattice basis, condition-number bound, or determinant hypothesis is retained.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Total archimedean place multiplicity. -/
def numberFieldInfinitePlaceWeight : ℝ :=
  ∑ w : InfinitePlace K, (mult w : ℝ)

theorem numberFieldInfinitePlaceWeight_pos :
    0 < numberFieldInfinitePlaceWeight (K := K) := by
  let w : InfinitePlace K := Classical.choice inferInstance
  apply Finset.sum_pos
  · intro i _
    by_cases h : i.IsReal <;> simp [InfinitePlace.mult, h]
  · exact ⟨w, Finset.mem_univ w⟩

/-- Multiplicity-weighted mean of a real profile on infinite places. -/
def numberFieldWeightedPlaceMean (f : InfinitePlace K → ℝ) : ℝ :=
  (∑ w : InfinitePlace K, (mult w : ℝ) * f w) /
    numberFieldInfinitePlaceWeight (K := K)

/-- Remove the weighted place mean. -/
def numberFieldCenteredPlaceProfile (f : InfinitePlace K → ℝ) :
    InfinitePlace K → ℝ :=
  fun w => f w - numberFieldWeightedPlaceMean f

theorem numberFieldCenteredPlaceProfile_mem_hyperplane
    (f : InfinitePlace K → ℝ) :
    numberFieldCenteredPlaceProfile f ∈
      numberFieldUnitPlaceLogHyperplane (K := K) := by
  change ∑ w : InfinitePlace K, (mult w : ℝ) *
      (f w - numberFieldWeightedPlaceMean f) = 0
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  dsimp [numberFieldWeightedPlaceMean]
  field_simp [ne_of_gt (numberFieldInfinitePlaceWeight_pos (K := K))]
  rw [numberFieldInfinitePlaceWeight]
  ring

/-- Average of the centered profiles across a nonempty coordinate family. -/
def numberFieldCenteredPlaceProfileAverage {n : ℕ}
    (f : Fin (n + 1) → InfinitePlace K → ℝ) : InfinitePlace K → ℝ :=
  (1 / (n + 1 : ℝ)) • ∑ i, numberFieldCenteredPlaceProfile (f i)

/-- Residual after removing both weighted place and coordinate means. -/
def numberFieldDoubleCenteredPlaceProfile {n : ℕ}
    (f : Fin (n + 1) → InfinitePlace K → ℝ) (i : Fin (n + 1)) :
    InfinitePlace K → ℝ :=
  numberFieldCenteredPlaceProfile (f i) - numberFieldCenteredPlaceProfileAverage f

theorem numberFieldDoubleCenteredPlaceProfile_mem_hyperplane {n : ℕ}
    (f : Fin (n + 1) → InfinitePlace K → ℝ) (i : Fin (n + 1)) :
    numberFieldDoubleCenteredPlaceProfile f i ∈
      numberFieldUnitPlaceLogHyperplane (K := K) := by
  apply (numberFieldUnitPlaceLogHyperplane (K := K)).sub_mem
  · exact numberFieldCenteredPlaceProfile_mem_hyperplane (f i)
  · apply (numberFieldUnitPlaceLogHyperplane (K := K)).smul_mem
    exact (numberFieldUnitPlaceLogHyperplane (K := K)).sum_mem fun j _ =>
      numberFieldCenteredPlaceProfile_mem_hyperplane (f j)

theorem sum_numberFieldDoubleCenteredPlaceProfile_eq_zero {n : ℕ}
    (f : Fin (n + 1) → InfinitePlace K → ℝ) :
    ∑ i, numberFieldDoubleCenteredPlaceProfile f i = 0 := by
  funext w
  simp only [numberFieldDoubleCenteredPlaceProfile, Pi.sub_apply, Finset.sum_sub_distrib,
    numberFieldCenteredPlaceProfileAverage, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, Pi.zero_apply]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]

/-- Half the negative double-centered residual, the target absorbed by diagonal congruence. -/
def numberFieldDetOneUnitBalanceTarget {n : ℕ}
    (f : Fin (n + 1) → InfinitePlace K → ℝ) (i : Fin (n + 1)) :
    InfinitePlace K → ℝ :=
  (-1 / 2 : ℝ) • numberFieldDoubleCenteredPlaceProfile f i

/-- Arbitrary logarithmic place weights become uniformly close to the sum of a coordinate-only
and a place-only profile after multiplication by a product-one tuple of units. -/
theorem exists_numberFieldDetOneUnit_logWeight_balancingRadius :
    ∃ R : ℝ, 0 < R ∧ ∀ (n : ℕ)
      (f : Fin (n + 1) → InfinitePlace K → ℝ),
      ∃ u : Fin (n + 1) → (𝓞 K)ˣ,
        (∏ i, u i = 1) ∧
        ∀ i w,
          |(f i w + 2 * numberFieldUnitPlaceLogEmbeddings (u i) w) -
              (numberFieldWeightedPlaceMean (f i) +
                numberFieldCenteredPlaceProfileAverage f w)| ≤
            2 * (n + 1 : ℝ) * R := by
  obtain ⟨R, hR, hcover⟩ :=
    exists_numberFieldDetOneUnitPlaceLog_coveringRadius (K := K)
  refine ⟨R, hR, ?_⟩
  intro n f
  let y : Fin (n + 1) → InfinitePlace K → ℝ :=
    fun i => numberFieldDetOneUnitBalanceTarget f i
  have hy (i : Fin (n + 1)) :
      y i ∈ numberFieldUnitPlaceLogHyperplane (K := K) := by
    apply (numberFieldUnitPlaceLogHyperplane (K := K)).smul_mem
    exact numberFieldDoubleCenteredPlaceProfile_mem_hyperplane f i
  have hysum : ∑ i, y i = 0 := by
    dsimp [y, numberFieldDetOneUnitBalanceTarget]
    rw [← Finset.smul_sum, sum_numberFieldDoubleCenteredPlaceProfile_eq_zero]
    simp
  obtain ⟨u, hu, hubound⟩ := hcover n y hy hysum
  refine ⟨u, hu, ?_⟩
  intro i w
  have heval :
      |numberFieldUnitPlaceLogEmbeddings (u i) w - y i w| ≤
        ‖numberFieldUnitPlaceLogEmbeddings (u i) - y i‖ := by
    simpa [Real.norm_eq_abs] using
      norm_le_pi_norm (numberFieldUnitPlaceLogEmbeddings (u i) - y i) w
  have hcoord := le_trans heval (hubound i)
  have hrearrange :
      (f i w + 2 * numberFieldUnitPlaceLogEmbeddings (u i) w) -
          (numberFieldWeightedPlaceMean (f i) +
            numberFieldCenteredPlaceProfileAverage f w) =
        2 * (numberFieldUnitPlaceLogEmbeddings (u i) w - y i w) := by
    dsimp [y, numberFieldDetOneUnitBalanceTarget,
      numberFieldDoubleCenteredPlaceProfile, numberFieldCenteredPlaceProfile]
    ring
  rw [hrearrange, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

end

end GaloisForLFunctions.HTGeometry

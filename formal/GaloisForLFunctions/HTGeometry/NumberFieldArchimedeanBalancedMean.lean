import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanBalancedSizeReduction

/-!
# Weighted means of determinant-balanced archimedean Jacobi data

The place profile used in determinant balancing has weighted mean zero.  Consequently the
coordinate constants occurring in an `IsDetBalanced` certificate are uniformly close to the
actual weighted means of the logarithmic Jacobi weights.  This removes the last arbitrary witness
from later leading-minor comparisons.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The weighted place mean is additive. -/
theorem numberFieldWeightedPlaceMean_add
    (f g : InfinitePlace K → ℝ) :
    numberFieldWeightedPlaceMean (fun w ↦ f w + g w) =
      numberFieldWeightedPlaceMean f + numberFieldWeightedPlaceMean g := by
  simp only [numberFieldWeightedPlaceMean, mul_add, Finset.sum_add_distrib]
  ring

/-- The weighted place mean commutes with subtraction. -/
theorem numberFieldWeightedPlaceMean_sub
    (f g : InfinitePlace K → ℝ) :
    numberFieldWeightedPlaceMean (fun w ↦ f w - g w) =
      numberFieldWeightedPlaceMean f - numberFieldWeightedPlaceMean g := by
  simp only [numberFieldWeightedPlaceMean, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The weighted place mean commutes with real scalar multiplication. -/
theorem numberFieldWeightedPlaceMean_mul
    (a : ℝ) (f : InfinitePlace K → ℝ) :
    numberFieldWeightedPlaceMean (fun w ↦ a * f w) =
      a * numberFieldWeightedPlaceMean f := by
  rw [numberFieldWeightedPlaceMean, numberFieldWeightedPlaceMean]
  have hsum : (∑ w : InfinitePlace K, (mult w : ℝ) * (a * f w)) =
      a * ∑ w : InfinitePlace K, (mult w : ℝ) * f w := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hsum]
  ring

/-- The weighted mean of a constant profile is that constant. -/
theorem numberFieldWeightedPlaceMean_const (a : ℝ) :
    numberFieldWeightedPlaceMean (fun _ : InfinitePlace K ↦ a) = a := by
  rw [numberFieldWeightedPlaceMean]
  have hsum : (∑ w : InfinitePlace K, (mult w : ℝ) * a) =
      numberFieldInfinitePlaceWeight (K := K) * a := by
    rw [numberFieldInfinitePlaceWeight, Finset.sum_mul]
  rw [hsum]
  field_simp [ne_of_gt (numberFieldInfinitePlaceWeight_pos (K := K))]

/-- Centering at the weighted place mean gives weighted mean zero. -/
theorem numberFieldWeightedPlaceMean_centeredPlaceProfile
    (f : InfinitePlace K → ℝ) :
    numberFieldWeightedPlaceMean (numberFieldCenteredPlaceProfile f) = 0 := by
  have h := numberFieldCenteredPlaceProfile_mem_hyperplane f
  change (∑ w : InfinitePlace K, (mult w : ℝ) *
      numberFieldCenteredPlaceProfile f w) = 0 at h
  rw [numberFieldWeightedPlaceMean, h, zero_div]

/-- The coordinate-average centered place profile also has weighted mean zero. -/
theorem numberFieldWeightedPlaceMean_centeredPlaceProfileAverage
    {m : ℕ} (f : Fin (m + 1) → InfinitePlace K → ℝ) :
    numberFieldWeightedPlaceMean (numberFieldCenteredPlaceProfileAverage f) = 0 := by
  have hp : numberFieldCenteredPlaceProfileAverage f ∈
      numberFieldUnitPlaceLogHyperplane (K := K) := by
    apply (numberFieldUnitPlaceLogHyperplane (K := K)).smul_mem
    exact (numberFieldUnitPlaceLogHyperplane (K := K)).sum_mem fun i _ ↦
      numberFieldCenteredPlaceProfile_mem_hyperplane (f i)
  change (∑ w : InfinitePlace K, (mult w : ℝ) *
      numberFieldCenteredPlaceProfileAverage f w) = 0 at hp
  rw [numberFieldWeightedPlaceMean, hp, zero_div]

/-- A pointwise absolute bound passes to the weighted place mean. -/
theorem abs_numberFieldWeightedPlaceMean_le
    {f : InfinitePlace K → ℝ} {R : ℝ}
    (hf : ∀ w, |f w| ≤ R) :
    |numberFieldWeightedPlaceMean f| ≤ R := by
  have hW : 0 < numberFieldInfinitePlaceWeight (K := K) :=
    numberFieldInfinitePlaceWeight_pos (K := K)
  have hmult (w : InfinitePlace K) : 0 ≤ (mult w : ℝ) := by
    by_cases hw : w.IsReal <;> simp [InfinitePlace.mult, hw]
  have habs :
      abs (∑ w : InfinitePlace K, (mult w : ℝ) * f w) ≤
        ∑ w : InfinitePlace K, (mult w : ℝ) * |f w| := by
    calc
      abs (∑ w : InfinitePlace K, (mult w : ℝ) * f w) ≤
          ∑ w : InfinitePlace K, |(mult w : ℝ) * f w| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ w : InfinitePlace K, (mult w : ℝ) * |f w| := by
        apply Finset.sum_congr rfl
        intro w _
        rw [abs_mul, abs_of_nonneg (hmult w)]
  have hsum :
      (∑ w : InfinitePlace K, (mult w : ℝ) * |f w|) ≤
        numberFieldInfinitePlaceWeight (K := K) * R := by
    rw [numberFieldInfinitePlaceWeight, Finset.sum_mul]
    exact Finset.sum_le_sum fun w _ ↦
      mul_le_mul_of_nonneg_left (hf w) (hmult w)
  rw [numberFieldWeightedPlaceMean, abs_div, abs_of_pos hW]
  apply (div_le_iff₀ hW).2
  calc
    abs (∑ w : InfinitePlace K, (mult w : ℝ) * f w) ≤
        ∑ w : InfinitePlace K, (mult w : ℝ) * |f w| := habs
    _ ≤ numberFieldInfinitePlaceWeight (K := K) * R := hsum
    _ = R * numberFieldInfinitePlaceWeight (K := K) := by ring

/-- Any coordinate witness for determinant balance is close to the actual weighted logarithmic
coordinate mean. -/
theorem numberFieldArchimedeanDetBalanced_mean_sub_witness_le
    {m : ℕ} {A : numberFieldArchimedeanPositiveForms K (m + 1)}
    (J : NumberFieldArchimedeanJacobiData A) (R : ℝ)
    (a : Fin (m + 1) → ℝ)
    (ha : ∀ i w,
      |Real.log (numberFieldArchimedeanJacobiWeight J i w) -
        (a i + numberFieldCenteredPlaceProfileAverage
          (fun j v ↦ Real.log (numberFieldArchimedeanJacobiWeight J j v)) w)| ≤ R) :
    ∀ i, |numberFieldWeightedPlaceMean
        (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J i w)) - a i| ≤ R := by
  intro i
  let p : InfinitePlace K → ℝ :=
    numberFieldCenteredPlaceProfileAverage
      (fun j w ↦ Real.log (numberFieldArchimedeanJacobiWeight J j w))
  let e : InfinitePlace K → ℝ := fun w ↦
    Real.log (numberFieldArchimedeanJacobiWeight J i w) - (a i + p w)
  have he : |numberFieldWeightedPlaceMean e| ≤ R :=
    abs_numberFieldWeightedPlaceMean_le (ha i)
  have hp : numberFieldWeightedPlaceMean p = 0 :=
    numberFieldWeightedPlaceMean_centeredPlaceProfileAverage _
  have hmean : numberFieldWeightedPlaceMean e =
      numberFieldWeightedPlaceMean
          (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J i w)) - a i := by
    calc
      numberFieldWeightedPlaceMean e =
          numberFieldWeightedPlaceMean
              (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J i w)) -
            numberFieldWeightedPlaceMean (fun w ↦ a i + p w) := by
        exact numberFieldWeightedPlaceMean_sub _ _
      _ = numberFieldWeightedPlaceMean
              (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J i w)) -
            (numberFieldWeightedPlaceMean (fun _ ↦ a i) +
              numberFieldWeightedPlaceMean p) := by
        rw [numberFieldWeightedPlaceMean_add]
      _ = numberFieldWeightedPlaceMean
              (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J i w)) - a i := by
        rw [numberFieldWeightedPlaceMean_const, hp, add_zero]
  rwa [hmean] at he

/-- In a determinant-balance certificate, every chosen coordinate constant is close to the actual
weighted logarithmic coordinate mean. -/
theorem NumberFieldArchimedeanJacobiData.IsDetBalanced.exists_mean_witness_close
    {m : ℕ} {A : numberFieldArchimedeanPositiveForms K (m + 1)}
    {J : NumberFieldArchimedeanJacobiData A} {R : ℝ}
    (h : J.IsDetBalanced R) :
    ∃ a : Fin (m + 1) → ℝ, ∀ i,
      |numberFieldWeightedPlaceMean
          (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J i w)) - a i| ≤ R := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, numberFieldArchimedeanDetBalanced_mean_sub_witness_le J R a ha⟩

end

end GaloisForLFunctions.HTGeometry

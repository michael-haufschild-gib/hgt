import GaloisForLFunctions.RHTower.Sieve.HeathBrownPrimitiveRayMassRealScale
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueTwoScale

/-!
# Real-ratio Heath--Brown sparse mean-value recurrence

Summing the unrestricted primitive-ray estimate over ordered sparse cofactor pairs gives the
literal real-ratio form of Heath--Brown's Lemma 6.  This is the quantitatively faithful recurrence
needed when the paper's selected auxiliary scale can exceed the original dense length.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Ordered-cofactor real-ratio collision-square recurrence. -/
theorem cast_card_heathBrownPositiveProductLogCollisionSquare_le_twoScale_realRatio_ordered
    {N N0 : ℕ} (hN0 : 1 ≤ N0)
    {m1 m2 : PNat} (hm : (m2 : ℕ) ≤ (m1 : ℕ))
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (#(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta) : ℝ) ≤
      19 * delta * (N : ℝ) ^ 2 +
        (2 * (N : ℝ) / (N0 : ℝ)) *
          (#(heathBrownPositiveProductLogCollisionSquare N0 m1 m2 delta) : ℝ) +
        3 * (N : ℝ) / (N0 : ℝ) := by
  rw [card_heathBrownPositiveProductLogCollisionSquare_eq_rayMass,
    card_heathBrownPositiveProductLogCollisionSquare_eq_rayMass]
  apply cast_heathBrownPrimitiveLogRayMass_le_twoScale_realRatio hN0
  · positivity
  · positivity
  · exact_mod_cast hm
  · exact hdelta0
  · exact hdelta1

/-- Unordered real-ratio collision-square recurrence. -/
theorem cast_card_heathBrownPositiveProductLogCollisionSquare_le_twoScale_realRatio
    {N N0 : ℕ} (hN0 : 1 ≤ N0) (m1 m2 : PNat)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (#(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta) : ℝ) ≤
      19 * delta * (N : ℝ) ^ 2 +
        (2 * (N : ℝ) / (N0 : ℝ)) *
          (#(heathBrownPositiveProductLogCollisionSquare N0 m1 m2 delta) : ℝ) +
        3 * (N : ℝ) / (N0 : ℝ) := by
  rcases le_total (m2 : ℕ) (m1 : ℕ) with hm | hm
  · exact cast_card_heathBrownPositiveProductLogCollisionSquare_le_twoScale_realRatio_ordered
      hN0 hm hdelta0 hdelta1
  · rw [card_heathBrownPositiveProductLogCollisionSquare_swap N m1 m2,
      card_heathBrownPositiveProductLogCollisionSquare_swap N0 m1 m2]
    exact cast_card_heathBrownPositiveProductLogCollisionSquare_le_twoScale_realRatio_ordered
      hN0 hm hdelta0 hdelta1

/-- Aggregate real-ratio collision recurrence. -/
theorem cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale_realRatio
    (A : Finset PNat) {N N0 : ℕ} (hN0 : 1 ≤ N0)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (heathBrownPositiveProductLogCollisionAggregate A N delta : ℝ) ≤
      19 * delta * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        (2 * (N : ℝ) / (N0 : ℝ)) *
          (heathBrownPositiveProductLogCollisionAggregate A N0 delta : ℝ) +
        (3 * (N : ℝ) / (N0 : ℝ)) * (A.card : ℝ) ^ 2 := by
  unfold heathBrownPositiveProductLogCollisionAggregate
  push_cast
  calc
    ∑ m1 ∈ A, ∑ m2 ∈ A,
        (#(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta) : ℝ) ≤
      ∑ m1 ∈ A, ∑ m2 ∈ A,
        (19 * delta * (N : ℝ) ^ 2 +
          (2 * (N : ℝ) / (N0 : ℝ)) *
            (#(heathBrownPositiveProductLogCollisionSquare N0 m1 m2 delta) : ℝ) +
          3 * (N : ℝ) / (N0 : ℝ)) := by
      apply Finset.sum_le_sum
      intro m1 hm1
      apply Finset.sum_le_sum
      intro m2 hm2
      exact cast_card_heathBrownPositiveProductLogCollisionSquare_le_twoScale_realRatio
        hN0 m1 m2 hdelta0 hdelta1
    _ = 19 * delta * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        (2 * (N : ℝ) / (N0 : ℝ)) *
          (∑ m1 ∈ A, ∑ m2 ∈ A,
            (#(heathBrownPositiveProductLogCollisionSquare N0 m1 m2 delta) : ℝ)) +
        (3 * (N : ℝ) / (N0 : ℝ)) * (A.card : ℝ) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      simp_rw [← Finset.mul_sum]
      ring

/-- Height-specialized real-ratio aggregate recurrence. -/
theorem cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale_inv_realRatio
    (A : Finset PNat) (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {N N0 : ℕ} (hN0 : 1 ≤ N0) :
    (heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) : ℝ) ≤
      19 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        (2 * (N : ℝ) / (N0 : ℝ)) *
          (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
        (3 * (N : ℝ) / (N0 : ℝ)) * (A.card : ℝ) ^ 2 := by
  apply cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale_realRatio A hN0
  · exact inv_pos.mpr T.property
  · exact (inv_le_one₀ T.property).mpr hT

/-- Source-facing real-ratio sparse mean-value estimate. -/
theorem integral_Icc_normSq_heathBrown_factors_le_twoScaleAggregate_realRatio
    (A B : Finset PNat) (eps : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {N N0 : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N) (hN0 : 1 ≤ N0) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        (19 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          (2 * (N : ℝ) / (N0 : ℝ)) *
            (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
          (3 * (N : ℝ) / (N0 : ℝ)) * (A.card : ℝ) ^ 2) := by
  calc
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        heathBrownPositiveWeightedCollision A B q T :=
      integral_Icc_normSq_heathBrown_factors_le_weightedCollision A B eps q T
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
        (heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (heathBrownPositiveWeightedCollision_le_collisionAggregate A B q T hB) (by positivity)
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
        (19 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          (2 * (N : ℝ) / (N0 : ℝ)) *
            (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
          (3 * (N : ℝ) / (N0 : ℝ)) * (A.card : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale_inv_realRatio
          A T hT hN0) (by positivity)

/-- Fully integral real-ratio form of Heath--Brown's two-scale recurrence. -/
theorem integral_Icc_normSq_heathBrown_factors_le_twoScaleIntegral_realRatio
    (A B : Finset PNat) (eps : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {N N0 : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N) (hN0 : 1 ≤ N0) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        (19 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          (2 * (N : ℝ) / (N0 : ℝ)) *
            ((5 / (2 * (T : ℝ))) *
              ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
                  (heathBrownHalfHeight T : ℝ),
                ‖heathBrownSparseFactor A (fun _ => 1) t *
                  heathBrownDenseFactor (heathBrownPositiveInterval N0 hN0)
                    heathBrownDenseUnitWeight t‖ ^ 2) +
          (3 * (N : ℝ) / (N0 : ℝ)) * (A.card : ℝ) ^ 2) := by
  calc
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        (19 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          (2 * (N : ℝ) / (N0 : ℝ)) *
            (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
          (3 * (N : ℝ) / (N0 : ℝ)) * (A.card : ℝ) ^ 2) :=
      integral_Icc_normSq_heathBrown_factors_le_twoScaleAggregate_realRatio
        A B eps q T hT hB hN0
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
        (19 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          (2 * (N : ℝ) / (N0 : ℝ)) *
            ((5 / (2 * (T : ℝ))) *
              ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
                  (heathBrownHalfHeight T : ℝ),
                ‖heathBrownSparseFactor A (fun _ => 1) t *
                  heathBrownDenseFactor (heathBrownPositiveInterval N0 hN0)
                    heathBrownDenseUnitWeight t‖ ^ 2) +
          (3 * (N : ℝ) / (N0 : ℝ)) * (A.card : ℝ) ^ 2) := by
      gcongr
      exact cast_heathBrownPositiveProductLogCollisionAggregate_le_halfHeightIntegral
        A T hN0

end

end RHTower.Sieve

import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueTwoScale

/-!
# Arbitrary-scale Heath--Brown sparse mean-value recurrence

Heath--Brown's Lemma 6 permits every positive auxiliary length `N0`.  The primitive-ray proof
only needs its nontrivial decomposition when `N0 ≤ N`; for `N < N0`, monotonicity of the closed
collision support gives the same displayed estimate directly.  This file removes the accidental
`N0 ≤ N` restriction from the integral recurrence.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Enlarging the dense cutoff enlarges the closed Heath--Brown collision aggregate. -/
theorem heathBrownPositiveProductLogCollisionAggregate_mono
    (A : Finset PNat) {N N0 : ℕ} (hNN0 : N ≤ N0) (delta : ℝ) :
    heathBrownPositiveProductLogCollisionAggregate A N delta ≤
      heathBrownPositiveProductLogCollisionAggregate A N0 delta := by
  rw [← card_heathBrownPositiveProductLogCollisionAggregateFinset,
    ← card_heathBrownPositiveProductLogCollisionAggregateFinset]
  apply Finset.card_le_card
  intro z hz
  rw [heathBrownPositiveProductLogCollisionAggregateFinset] at hz ⊢
  have hz' := Finset.mem_filter.mp hz
  have hp := Finset.mem_product.mp hz'.1
  have hp1 := Finset.mem_product.mp hp.1
  have hp2 := Finset.mem_product.mp hp.2
  have hn1 := Finset.mem_Icc.mp hp1.2
  have hn2 := Finset.mem_Icc.mp hp2.2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hz'.2⟩
  · exact Finset.mem_product.mpr
      ⟨hp1.1, Finset.mem_Icc.mpr ⟨hn1.1, hn1.2.trans hNN0⟩⟩
  · exact Finset.mem_product.mpr
      ⟨hp2.1, Finset.mem_Icc.mpr ⟨hn2.1, hn2.2.trans hNN0⟩⟩

/-- Heath--Brown's aggregate two-scale inequality for every positive auxiliary cutoff. -/
theorem cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale_arbitrary
    (A : Finset PNat) {N N0 : ℕ} (hN0 : 1 ≤ N0)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (heathBrownPositiveProductLogCollisionAggregate A N delta : ℝ) ≤
      15 * delta * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        ((N / N0 + 1 : ℕ) : ℝ) *
          (heathBrownPositiveProductLogCollisionAggregate A N0 delta : ℝ) +
        ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2 := by
  by_cases hN0N : N0 ≤ N
  · exact cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale
      A hN0 hN0N hdelta0 hdelta1
  · have hNN0 : N < N0 := Nat.lt_of_not_ge hN0N
    have hmono :
        (heathBrownPositiveProductLogCollisionAggregate A N delta : ℝ) ≤
          (heathBrownPositiveProductLogCollisionAggregate A N0 delta : ℝ) := by
      exact_mod_cast heathBrownPositiveProductLogCollisionAggregate_mono A hNN0.le delta
    rw [Nat.div_eq_of_lt hNN0]
    norm_num
    calc
      (heathBrownPositiveProductLogCollisionAggregate A N delta : ℝ) ≤
          (heathBrownPositiveProductLogCollisionAggregate A N0 delta : ℝ) := hmono
      _ ≤ 15 * delta * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          (heathBrownPositiveProductLogCollisionAggregate A N0 delta : ℝ) +
          (A.card : ℝ) ^ 2 := by
        have hdiag : 0 ≤ 15 * delta * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by
          positivity
        have hcard : 0 ≤ (A.card : ℝ) ^ 2 := sq_nonneg _
        linarith

/-- Height-specialized arbitrary-scale aggregate recurrence. -/
theorem cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale_inv_arbitrary
    (A : Finset PNat) (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {N N0 : ℕ} (hN0 : 1 ≤ N0) :
    (heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) : ℝ) ≤
      15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        ((N / N0 + 1 : ℕ) : ℝ) *
          (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
        ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2 := by
  apply cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale_arbitrary A hN0
  · exact inv_pos.mpr T.property
  · exact (inv_le_one₀ T.property).mpr hT

/-- Source-facing arbitrary-scale two-scale sparse mean-value estimate. -/
theorem integral_Icc_normSq_heathBrown_factors_le_twoScaleAggregate_arbitrary
    (A B : Finset PNat) (eps : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {N N0 : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N) (hN0 : 1 ≤ N0) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          ((N / N0 + 1 : ℕ) : ℝ) *
            (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
          ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2) := by
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
        (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          ((N / N0 + 1 : ℕ) : ℝ) *
            (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
          ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale_inv_arbitrary
          A T hT hN0) (by positivity)

/-- Fully integral arbitrary-scale form of Heath--Brown's two-scale recurrence. -/
theorem integral_Icc_normSq_heathBrown_factors_le_twoScaleIntegral_arbitrary
    (A B : Finset PNat) (eps : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {N N0 : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N) (hN0 : 1 ≤ N0) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          ((N / N0 + 1 : ℕ) : ℝ) *
            ((5 / (2 * (T : ℝ))) *
              ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
                  (heathBrownHalfHeight T : ℝ),
                ‖heathBrownSparseFactor A (fun _ => 1) t *
                  heathBrownDenseFactor (heathBrownPositiveInterval N0 hN0)
                    heathBrownDenseUnitWeight t‖ ^ 2) +
          ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2) := by
  calc
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          ((N / N0 + 1 : ℕ) : ℝ) *
            (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
          ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2) :=
      integral_Icc_normSq_heathBrown_factors_le_twoScaleAggregate_arbitrary
        A B eps q T hT hB hN0
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
        (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          ((N / N0 + 1 : ℕ) : ℝ) *
            ((5 / (2 * (T : ℝ))) *
              ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
                  (heathBrownHalfHeight T : ℝ),
                ‖heathBrownSparseFactor A (fun _ => 1) t *
                  heathBrownDenseFactor (heathBrownPositiveInterval N0 hN0)
                    heathBrownDenseUnitWeight t‖ ^ 2) +
          ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2) := by
      gcongr
      exact cast_heathBrownPositiveProductLogCollisionAggregate_le_halfHeightIntegral
        A T hN0

end

end RHTower.Sieve

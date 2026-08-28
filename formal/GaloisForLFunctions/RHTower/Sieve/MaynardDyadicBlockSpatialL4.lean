import GaloisForLFunctions.RHTower.Sieve.MaynardSpatialMellinL4
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockSpatialL2

/-!
# Maynard equation (112) for the observed Heath--Brown block

This module inserts the actual observed eligible dyadic aggregate into the
spatial fourth-moment theorem.  Bad physical bases pay exact selected-cell
additive energy `R*`, rather than its universal cubic cardinality bound.
-/

open Complex MeasureTheory

noncomputable section
namespace RHTower.Sieve

/-- At the critical line, source amplitude `V` gives fixed-ambient
defect-cell coefficient bound `2V`. -/
theorem norm_maynardFixedAmbientDefectCellCoefficient_le_two_mul_of_source_bound
    {a : ℝ → ℂ} {N R H V : ℝ} {m : ℕ} {u : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hV0 : 0 ≤ V)
    (hsource : ‖a ((m : ℝ) + u)‖ ≤ V) :
    ‖maynardFixedAmbientDefectCellCoefficient a N R H 1 m u‖ ≤ 2 * V := by
  have hKR0 := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
    hN hR (s := (1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) (by simp)
  have hKH0 := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
    hN hH (s := (1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) (by simp)
  have hKR : ‖routeTNormalizedSmoothWindowMellin N R
      ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 1 := by
    simpa using hKR0
  have hKH : ‖routeTNormalizedSmoothWindowMellin N H
      ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 1 := by
    simpa using hKH0
  have hkernel :
      ‖routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) -
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 2 := by
    calc
      _ ≤ ‖routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ +
          ‖routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hKR hKH
      _ = 2 := by norm_num
  rw [maynardFixedAmbientDefectCellCoefficient, norm_mul]
  calc
    ‖a ((m : ℝ) + u)‖ *
        ‖routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤
        V * 2 := mul_le_mul hsource hkernel (norm_nonneg _) hV0
    _ = 2 * V := by ring

/-- Critical-line equation-(112) fourth moment for a continuous source
bounded by `V` on selected cells. -/
theorem integral_norm_four_maynardFixedAmbientPhysicalDefectPacket_le_rstar_of_source_bound
    {x N R H V : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hV0 : 0 ≤ V) (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (a : ℝ → ℂ) (ha : Continuous a)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ V) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖ ^ 4) ≤
      4 * (2 * x) * (1 + 2 * (1 + Real.log (2 * cellCount))) *
        (2 * V) ^ 4 *
          (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ) := by
  have hbnd : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient a N R H 1 m u‖ ≤ 2 * V := by
    intro m hm u hu
    exact norm_maynardFixedAmbientDefectCellCoefficient_le_two_mul_of_source_bound
      hN hR hH hV0 (hV m hm u hu)
  have hL4 := integral_norm_four_maynardFixedAmbientPhysicalDefectPacket_le_rstar
    (x := x) (sigma := (1 : ℝ)) (A := 2 * V) (cellCount := cellCount)
    hx (by norm_num) (mul_nonneg (by norm_num) hV0)
    hN hR hH S hS a ha hbnd
  simpa only [sub_self, mul_zero, zero_add, Real.rpow_one] using hL4

/-- Critical-line equation-(112) bad-base theorem for a continuous source
bounded by `V` on selected cells. -/
theorem volume_maynardFixedAmbientPhysicalDefectPacket_large_le_rstar_of_source_bound
    {x N R H V D : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hV0 : 0 ≤ V) (hD : 0 < D)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (a : ℝ → ℂ) (ha : Continuous a)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ V) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖} ≤
      (4 * (2 * x) * (1 + 2 * (1 + Real.log (2 * cellCount))) *
        (2 * V) ^ 4 *
          (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ)) / D ^ 4 := by
  apply volume_maynardFixedAmbientPhysicalDefectPacket_large_le_rstar
    hx hN hR hH (mul_nonneg (by norm_num) hV0) hD S hS a ha
  intro m hm u hu
  exact norm_maynardFixedAmbientDefectCellCoefficient_le_two_mul_of_source_bound
    hN hR hH hV0 (hV m hm u hu)

/-- Equation-(112) for the actual observed Heath--Brown dyadic aggregate.
Bad physical bases pay exact selected-cell additive energy `R*`. -/
theorem volume_maynardDyadicBlockObservedPhysicalDefectPacket_large_le_rstar_of_selected_bound
    (L X k : ℕ) (T0 t : ℝ) {x N R H V D : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hV0 : 0 ≤ V) (hD : 0 < D)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I)‖ ≤ V) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖} ≤
      (4 * (2 * x) * (1 + 2 * (1 + Real.log (2 * cellCount))) *
        (2 * V) ^ 4 *
          (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ)) / D ^ 4 := by
  let a : ℝ → ℂ := fun y =>
    heathBrownObservedEligibleDyadicAggregate L X k T0 t
      (x * N) (maynardDyadicBlockObservationRadius x N R)
      ((1 : ℂ) + (y : ℝ) * I)
  have ha : Continuous a :=
    continuous_heathBrownObservedEligibleDyadicAggregate_line
      L X k T0 t (x * N) (maynardDyadicBlockObservationRadius x N R) 1
  simpa only [a] using
    volume_maynardFixedAmbientPhysicalDefectPacket_large_le_rstar_of_source_bound
      hx hN hR hH hV0 hD S hS a ha hV

end RHTower.Sieve

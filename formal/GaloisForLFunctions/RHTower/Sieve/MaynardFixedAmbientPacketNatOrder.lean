import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientPacketInterval
import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceArbitraryOrderLocalization

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Arbitrary-order tail localization with source aggregate frozen independently of the physical
Mellin base. -/
theorem exists_integral_norm_fixedSource_mul_adjacentKernel_natOrder_tail_le
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ (L X k : ℕ) (T0 t : ℝ) {M N H R U : ℝ},
        1 ≤ X → 0 < M → 1 ≤ N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N → 0 < U →
        ∫ y in {y : ℝ | U ≤ |y|},
          ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
                ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖ ≤
          heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
            (Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ))) := by
  obtain ⟨Cj, hCj, htail⟩ :=
    exists_integral_routeTAdjacentNormalizedKernel_one_natOrder_tail_le j hj
  refine ⟨Cj, hCj, ?_⟩
  intro L X k T0 t M N H R U hX hM hN hH hR hHR hRH hRN hU
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + (y : ℝ) * Complex.I) -
      routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * Complex.I)
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k M 1
  let tail : Set ℝ := {y : ℝ | U ≤ |y|}
  have hA : ∀ y : ℝ, ‖A y‖ ≤ P := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t M 1 y hM (by norm_num)
  have hP : 0 ≤ P := (norm_nonneg (A 0)).trans (hA 0)
  have hKint : Integrable K := by
    exact (integrable_routeTNormalizedSmoothWindowMellin_one
      (zero_lt_one.trans_le hN) hR).sub
      (integrable_routeTNormalizedSmoothWindowMellin_one
        (zero_lt_one.trans_le hN) hH)
  have hAcont : Continuous A :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t M 1
  have hprod : Integrable (fun y => ‖A y * K y‖) := by
    exact (hKint.bdd_mul hAcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hA)).norm
  have hmono : (∫ y in tail, ‖A y * K y‖) ≤
      ∫ y in tail, P * ‖K y‖ := by
    apply setIntegral_mono_on hprod.integrableOn
      (hKint.norm.const_mul P).integrableOn
        (measurableSet_le measurable_const continuous_abs.measurable)
    intro y _hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA y) (norm_nonneg _)
  have hscale : (∫ y in tail, P * ‖K y‖) =
      P * ∫ y in tail, ‖K y‖ := by
    rw [MeasureTheory.integral_const_mul]
  have hktail := htail N H R U hN hH hR hHR hRH hRN hU
  calc
    (∫ y in {y : ℝ | U ≤ |y|},
        ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
              ((1 : ℂ) + (y : ℝ) * Complex.I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * Complex.I))‖) =
        ∫ y in tail, ‖A y * K y‖ := by rfl
    _ ≤ ∫ y in tail, P * ‖K y‖ := hmono
    _ = P * ∫ y in tail, ‖K y‖ := hscale
    _ ≤ P * (Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ))) :=
      mul_le_mul_of_nonneg_left (by simpa [tail, K] using hktail) hP
    _ = _ := by rfl

/-- Arbitrary-order tail decay places a large frozen-source full defect into the literal range
packet once the displayed order-`j` tail is at most half the defect. -/
theorem exists_large_range_fixedAmbientPhysicalDefectPacket_of_full_defect_natOrder
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ (L X k K : ℕ) (T0 t : ℝ) {M lambda N H R B : ℝ},
        1 ≤ X → 0 < M → 0 < lambda → 0 < N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N → 1 ≤ lambda * N → 0 < B → 0 < K →
        heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
            (Cj * ((lambda * N) / (lambda * R)) ^ (j + 1) *
              (K : ℝ) ^ (-(j : ℝ))) ≤ B / 2 →
        B ≤ ‖∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
                ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖ →
        B / 8 ≤ ‖maynardFixedAmbientPhysicalDefectPacket (Finset.range K)
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda N R H 1‖ := by
  obtain ⟨Cj, hCj, htail⟩ :=
    exists_integral_norm_fixedSource_mul_adjacentKernel_natOrder_tail_le j hj
  refine ⟨Cj, hCj, ?_⟩
  intro L X k K T0 t M lambda N H R B hX hM hlambda hN hH hR hHR hRH hRN
    hphysicalNone hB hK htailSmall hfull
  have hphysicalN : 0 < lambda * N := mul_pos hlambda hN
  have hphysicalH : 0 < lambda * H := mul_pos hlambda hH
  have hphysicalR : 0 < lambda * R := mul_pos hlambda hR
  have hphysicalHR : lambda * H ≤ lambda * R :=
    mul_le_mul_of_nonneg_left hHR hlambda.le
  have hphysicalRH : lambda * R ≤ 2 * (lambda * H) := by nlinarith
  have hphysicalRN : lambda * R ≤ lambda * N :=
    mul_le_mul_of_nonneg_left hRN hlambda.le
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  let f : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
          ((1 : ℂ) + (y : ℝ) * Complex.I) *
      (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
          ((1 : ℂ) + (y : ℝ) * Complex.I))
  have hsourceCont : Continuous (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
        ((1 : ℂ) + (y : ℝ) * Complex.I)) :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t M 1
  have hsourceBound : ∀ y : ℝ,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
        ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤
        heathBrownWindowRelevantFixedPolylogBound L X k M 1 := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t M 1 y hM (by norm_num)
  have hkint : Integrable (fun y : ℝ =>
      routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
          ((1 : ℂ) + (y : ℝ) * Complex.I)) :=
    (integrable_routeTNormalizedSmoothWindowMellin_one hphysicalN hphysicalR).sub
      (integrable_routeTNormalizedSmoothWindowMellin_one hphysicalN hphysicalH)
  have hf : Integrable f := by
    exact hkint.bdd_mul hsourceCont.aestronglyMeasurable
      (Filter.Eventually.of_forall hsourceBound)
  have htailBound := htail L X k T0 t hX hM hphysicalNone hphysicalH hphysicalR
    hphysicalHR hphysicalRH hphysicalRN hKreal
  have hannulusRaw := norm_setIntegral_annulus_ge_of_low_tail
    hf (B := B) (U := 0) (V := (K : ℝ)) (E₀ := 0) (E₁ := B / 2)
    (by norm_num) hKreal.le (by simpa only [f] using hfull)
    (by simp) (htailBound.trans htailSmall)
  have hannulus : B / 2 ≤ ‖∫ y in {y : ℝ | 0 ≤ |y| ∧ |y| < (K : ℝ)}, f y‖ := by
    linarith
  have hconj : ∀ y : ℝ, f (-y) = (starRingEnd ℂ) (f y) := by
    intro y
    exact (conj_fixedSource_mul_adjacentKernel
      L X k T0 t M (lambda * N) (lambda * H) (lambda * R) y).symm
  have hwing := exists_positive_interval_norm_ge_quarter_of_annulus_of_conj
    hf hconj (B := B / 2) (U := 0) (T := (K : ℝ)) (V := (K : ℝ))
      (by norm_num) hKreal.le (le_refl _) hannulus
  have hpositive : B / 8 ≤ ‖∫ y in (0 : ℝ)..(K : ℝ), f y‖ := by
    rcases hwing with hwing | hzero
    · convert hwing using 1
      ring
    · simp only [intervalIntegral.integral_same, norm_zero] at hzero
      linarith
  have hpacket := maynardFixedAmbientPhysicalDefectPacket_range_eq_intervalIntegral
    (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
        ((1 : ℂ) + (y : ℝ) * Complex.I)) hsourceCont
      lambda N R H 1 K hphysicalN hphysicalR hphysicalH (by norm_num)
  rw [hpacket]
  dsimp only [f] at hpositive
  convert hpositive using 1
  norm_num

end

end RHTower.Sieve

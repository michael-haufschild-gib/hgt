import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientSpatialBridge
import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentAggregateCellExtraction
import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentAggregateReflection

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Consecutive positive unit cells tile the interval from zero to their natural cutoff. -/
theorem intervalIntegral_sum_range_unitCells_eq
    {f : ℝ → ℂ} (hf : Continuous f) (K : ℕ) :
    (∫ v : ℝ in (0 : ℝ)..1, ∑ m ∈ Finset.range K, f ((m : ℝ) + v)) =
      ∫ y : ℝ in (0 : ℝ)..(K : ℝ), f y := by
  induction K with
  | zero => simp
  | succ K ih =>
      simp_rw [Finset.sum_range_succ]
      have hsumCont : Continuous (fun v : ℝ =>
          ∑ m ∈ Finset.range K, f ((m : ℝ) + v)) := by
        fun_prop
      have hcellCont : Continuous (fun v : ℝ => f ((K : ℝ) + v)) := by
        fun_prop
      rw [intervalIntegral.integral_add
        (hsumCont.intervalIntegrable _ _) (hcellCont.intervalIntegrable _ _)]
      rw [ih]
      have hshift :
          (∫ v : ℝ in (0 : ℝ)..1, f ((K : ℝ) + v)) =
            ∫ y : ℝ in (K : ℝ)..((K : ℝ) + 1), f y := by
        rw [intervalIntegral.integral_comp_add_left f (K : ℝ)]
        simp
      rw [hshift, Nat.cast_succ]
      exact intervalIntegral.integral_add_adjacent_intervals
        (a := (0 : ℝ)) (b := (K : ℝ)) (c := (K : ℝ) + 1)
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- The fixed-ambient packet on all cells below `K` is exactly the positive-wing adjacent defect
truncated at the natural ordinate cutoff `K`. -/
theorem maynardFixedAmbientPhysicalDefectPacket_range_eq_intervalIntegral
    (a : ℝ → ℂ) (ha : Continuous a)
    (lambda N R H sigma : ℝ) (K : ℕ)
    (hN : 0 < lambda * N) (hR : 0 < lambda * R)
    (hH : 0 < lambda * H) (hsigma : 0 < sigma) :
    maynardFixedAmbientPhysicalDefectPacket (Finset.range K) a
        lambda N R H sigma =
      ∫ y : ℝ in (0 : ℝ)..(K : ℝ),
        a y *
          (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
              ((sigma : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
              ((sigma : ℂ) + (y : ℝ) * Complex.I)) := by
  let f : ℝ → ℂ := fun y =>
    a y *
      (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
          ((sigma : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
          ((sigma : ℂ) + (y : ℝ) * Complex.I))
  have hf : Continuous f := by
    exact ha.mul
      ((continuous_routeTNormalizedSmoothWindowMellin_line hN hR hsigma).sub
        (continuous_routeTNormalizedSmoothWindowMellin_line hN hH hsigma))
  unfold maynardFixedAmbientPhysicalDefectPacket
  simpa only [f] using intervalIntegral_sum_range_unitCells_eq hf K

/-- Tail localization with source aggregate frozen independently of the physical Mellin base. -/
theorem exists_integral_norm_fixedSource_mul_adjacentKernel_tail_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (L X k : ℕ) (T0 t : ℝ) {M N H R U : ℝ},
        1 ≤ X → 0 < M → 0 < N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N → 0 < U →
        ∫ y in {y : ℝ | U ≤ |y|},
          ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
                ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖ ≤
          heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
            (130 * C * (N / R) ^ (2 : ℕ) / U) := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_routeTAdjacentNormalizedKernel_one_general_tail_le
  refine ⟨C, hC, ?_⟩
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
    exact (integrable_routeTNormalizedSmoothWindowMellin_one hN hR).sub
      (integrable_routeTNormalizedSmoothWindowMellin_one hN hH)
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
    _ ≤ P * (130 * C * (N / R) ^ (2 : ℕ) / U) :=
      mul_le_mul_of_nonneg_left (by simpa [tail, K] using hktail) hP
    _ = _ := by rfl

/-- Exact conjugate reflection when the source packet is frozen at a base independent of the
physical Mellin kernel. -/
theorem conj_fixedSource_mul_adjacentKernel
    (L X k : ℕ) (T0 t M N H R y : ℝ) :
    (starRingEnd ℂ)
        (heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * Complex.I))) =
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
          ((1 : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) := by
  rw [map_mul, map_sub,
    conj_heathBrownWindowRelevantEligibleDyadicAggregate,
    conj_routeTNormalizedSmoothWindowMellin,
    conj_routeTNormalizedSmoothWindowMellin]
  congr 1 <;> simp

/-- A large full defect of the fixed source enters the literal finite packet consumed by the
spatial `L²` estimate once the explicit Mellin tail is at most half the defect. -/
theorem exists_large_range_fixedAmbientPhysicalDefectPacket_of_full_defect :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (L X k K : ℕ) (T0 t : ℝ) {M lambda N H R B : ℝ},
        1 ≤ X → 0 < M → 0 < lambda → 0 < N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N → 0 < B → 0 < K →
        heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
            (130 * C * ((lambda * N) / (lambda * R)) ^ (2 : ℕ) / (K : ℝ)) ≤ B / 2 →
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
  obtain ⟨C, hC, htail⟩ := exists_integral_norm_fixedSource_mul_adjacentKernel_tail_le
  refine ⟨C, hC, ?_⟩
  intro L X k K T0 t M lambda N H R B hX hM hlambda hN hH hR hHR hRH hRN
    hB hK htailSmall hfull
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
  have htailBound := htail L X k T0 t hX hM hphysicalN hphysicalH hphysicalR
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

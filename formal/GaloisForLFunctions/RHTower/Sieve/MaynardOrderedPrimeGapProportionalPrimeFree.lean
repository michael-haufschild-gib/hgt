import GaloisForLFunctions.RHTower.Sieve.MaynardOrderedPrimeGapOccupancy
import GaloisForLFunctions.RHTower.Sieve.MaynardPolynomialPrimeFreePhysicalDefect
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockPerron

open Complex MeasureTheory Set
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Fixed relative target half-width whose physical dilation at base `lambda` reserves at most
the full dyadic gap scale throughout one physical dyadic block. -/
def routeTPrimeGapProportionalTargetHalfWidth (k j : ℕ) : ℝ :=
  routeTPrimeGapDyadicScale j / (4 * routeTPrimeGapDyadicBase k)

theorem routeTPrimeGapProportionalTargetHalfWidth_pos (k j : ℕ) :
    0 < routeTPrimeGapProportionalTargetHalfWidth k j := by
  unfold routeTPrimeGapProportionalTargetHalfWidth
  exact div_pos (routeTPrimeGapDyadicScale_pos j)
    (mul_pos (by norm_num) (routeTPrimeGapDyadicBase_pos k))

/-- A base reserving a prime-free interval of length `h` also reserves every shorter nonnegative
target window. -/
theorem chebyshevTheta_subwindow_eq_zero_of_mem_primeGapOccupancyInterval
    {n : ℕ} {h w lambda : ℝ} (hw0 : 0 ≤ w) (hwh : w ≤ h)
    (hlambda : lambda ∈ routeTPrimeGapOccupancyInterval n h) :
    Chebyshev.theta (lambda + w) - Chebyshev.theta lambda = 0 := by
  apply chebyshevTheta_window_eq_zero_of_mem_primeGapOccupancyInterval hw0
  simpa only [routeTPrimeGapOccupancyInterval, Set.mem_Ico] using
    And.intro hlambda.1 (by linarith [hlambda.2])

theorem two_mul_routeTPrimeGapProportionalTargetHalfWidth_le_scale
    {k j : ℕ} {lambda : ℝ}
    (hlambda : lambda ≤ 2 * routeTPrimeGapDyadicBase k) :
    2 * (lambda * routeTPrimeGapProportionalTargetHalfWidth k j) ≤
      routeTPrimeGapDyadicScale j := by
  have hx := routeTPrimeGapDyadicBase_pos k
  have hh := routeTPrimeGapDyadicScale_pos j
  unfold routeTPrimeGapProportionalTargetHalfWidth
  rw [show 2 * (lambda *
      (routeTPrimeGapDyadicScale j / (4 * routeTPrimeGapDyadicBase k))) =
    (2 * lambda * routeTPrimeGapDyadicScale j) /
      (4 * routeTPrimeGapDyadicBase k) by ring]
  apply (div_le_iff₀ (show 0 < 4 * routeTPrimeGapDyadicBase k by positivity)).2
  nlinarith

/-- Literal ordered-prime-gap occupancy is prime-free for the proportional target geometry used
by the fixed-ambient Mellin packet. -/
theorem routeTPrimeGapDyadicBlockOccupancy_subset_proportionalPrimeFree (k j : ℕ) :
    routeTPrimeGapDyadicBlockOccupancy k j ⊆
      {lambda : ℝ |
        Chebyshev.theta
            (lambda + 2 * (lambda *
              routeTPrimeGapProportionalTargetHalfWidth k j)) -
          Chebyshev.theta lambda = 0} := by
  intro lambda hlambda
  have hblock := routeTPrimeGapDyadicBlockOccupancy_subset_block k j hlambda
  simp only [routeTPrimeGapDyadicBlockOccupancy, Set.mem_iUnion] at hlambda
  obtain ⟨n, _hn, hlambda⟩ := hlambda
  exact chebyshevTheta_subwindow_eq_zero_of_mem_primeGapOccupancyInterval
    (mul_nonneg (by norm_num) (mul_nonneg
      ((routeTPrimeGapDyadicBase_pos k).le.trans hblock.1)
      (routeTPrimeGapProportionalTargetHalfWidth_pos k j).le))
    (two_mul_routeTPrimeGapProportionalTargetHalfWidth_le_scale hblock.2)
    hlambda

/-- Gap-square occupancy in one dyadic shell is controlled by the bad-base measure for exactly
the proportional target width accepted by Maynard's fixed-ambient spatial `L²` theorem. -/
theorem sum_primeGapSquare_le_eight_mul_proportionalPrimeFree_block_measure (k j : ℕ) :
    (∑ n ∈ routeTPrimeGapDyadicBlockShell k j,
        xiHeatCassiniOrderedPrimeGap n ^ (2 : ℕ)) ≤
      8 * routeTPrimeGapDyadicScale j *
        (volume.restrict
          (Set.Icc (routeTPrimeGapDyadicBase k)
            (2 * routeTPrimeGapDyadicBase k))).real
          {lambda : ℝ |
            Chebyshev.theta
                (lambda + 2 * (lambda *
                  routeTPrimeGapProportionalTargetHalfWidth k j)) -
              Chebyshev.theta lambda = 0} := by
  refine (sum_primeGapSquare_le_eight_mul_volume_occupancy k j).trans ?_
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by norm_num) (routeTPrimeGapDyadicScale_pos j).le)
  let B := Set.Icc (routeTPrimeGapDyadicBase k) (2 * routeTPrimeGapDyadicBase k)
  let P : Set ℝ := {lambda : ℝ |
    Chebyshev.theta
        (lambda + 2 * (lambda *
          routeTPrimeGapProportionalTargetHalfWidth k j)) -
      Chebyshev.theta lambda = 0}
  have hoccBlock : routeTPrimeGapDyadicBlockOccupancy k j ⊆ B :=
    routeTPrimeGapDyadicBlockOccupancy_subset_block k j
  have hoccPrimeFree : routeTPrimeGapDyadicBlockOccupancy k j ⊆ P :=
    routeTPrimeGapDyadicBlockOccupancy_subset_proportionalPrimeFree k j
  have hfiniteP : (volume.restrict B) P ≠ ⊤ := by
    apply ne_of_lt
    calc
      (volume.restrict B) P ≤ (volume.restrict B) Set.univ :=
        measure_mono (Set.subset_univ P)
      _ = volume B := Measure.restrict_apply_univ B
      _ < ⊤ := by
        dsimp only [B]
        exact isCompact_Icc.measure_lt_top
  have hmono : (volume.restrict B).real
      (routeTPrimeGapDyadicBlockOccupancy k j) ≤
      (volume.restrict B).real P :=
    measureReal_mono hoccPrimeFree hfiniteP
  have hoccMeas : MeasurableSet (routeTPrimeGapDyadicBlockOccupancy k j) := by
    exact MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun _hn => measurableSet_Ico
  have hrestrictOcc :
      (volume.restrict B).real (routeTPrimeGapDyadicBlockOccupancy k j) =
        volume.real (routeTPrimeGapDyadicBlockOccupancy k j) := by
    rw [Measure.real, Measure.real, Measure.restrict_apply hoccMeas]
    have hinter :
        routeTPrimeGapDyadicBlockOccupancy k j ∩ B =
          routeTPrimeGapDyadicBlockOccupancy k j :=
      Set.inter_eq_left.mpr hoccBlock
    rw [hinter]
  simpa only [B, P, hrestrictOcc] using hmono

/-- The stopped comparable-width ladder commutes exactly with nonnegative physical dilation. -/
theorem routeTComparableWidthLadder_mul_left
    {lambda H R : ℝ} (hlambda : 0 ≤ lambda) (j : ℕ) :
    routeTComparableWidthLadder (lambda * H) (lambda * R) j =
      lambda * routeTComparableWidthLadder H R j := by
  unfold routeTComparableWidthLadder
  have hdiv :
      (lambda * R) / (((2 ^ j : ℕ) : ℝ)) =
        lambda * (R / (((2 ^ j : ℕ) : ℝ))) := by ring
  rw [hdiv]
  by_cases h : H ≤ R / (((2 ^ j : ℕ) : ℝ))
  · rw [max_eq_right h,
      max_eq_right (mul_le_mul_of_nonneg_left h hlambda)]
  · have h' : R / (((2 ^ j : ℕ) : ℝ)) ≤ H := le_of_not_ge h
    rw [max_eq_left h',
      max_eq_left (mul_le_mul_of_nonneg_left h' hlambda)]

/-- A polynomial-width prime-free target in a physical dyadic block produces a large adjacent
defect carried by one source packet fixed at the block's left endpoint.  The selected stopped
ladder rung is scale-free; all physical dependence is the single dilation parameter `lambda`. -/
theorem exists_eventually_routeT_proportional_primeFree_leftWindowRelevant_defect
    {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ lambda : ℝ in Filter.atTop,
      ∀ (L X k : ℕ) {T0 t x H0 : ℝ},
        0 < x → lambda ∈ Set.Icc x (2 * x) →
        0 < H0 → H0 ≤ 1 / 4 →
        X < (L + 1) ^ k →
        1 < T0 →
        ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ lambda →
        lambda ^ theta ≤ lambda * H0 →
        lambda + 2 * (lambda / 4) ≤ X →
        Chebyshev.theta (lambda + 2 * (lambda * H0)) -
            Chebyshev.theta lambda = 0 →
        ∃ J : ℕ, 0 < J ∧
          (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ (1 / 4) / H0 ∧
          ∃ j ∈ Finset.range J,
          ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (J : ℝ) ≤
            ‖∫ y : ℝ,
              heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
                  ((1 : ℂ) + (y : ℝ) * Complex.I) *
                (routeTNormalizedSmoothWindowMellin lambda
                    (lambda * routeTComparableWidthLadder H0 (1 / 4) j)
                    ((1 : ℂ) + (y : ℝ) * Complex.I) -
                  routeTNormalizedSmoothWindowMellin lambda
                    (lambda * routeTComparableWidthLadder H0 (1 / 4) (j + 1))
                    ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
  filter_upwards [exists_eventually_routeT_polynomial_primeFree_physicalSlice_defect htheta,
    Filter.eventually_ge_atTop (2 : ℝ)] with lambda hproducer hlambdaTwo
  intro L X k T0 t x H0 hx hlambda hH0 hH0quarter hXL hT0 hscale hpower
    hsupport hprimeFree
  have hlambda0 : 0 < lambda := by linarith
  have hphysicalH : 0 < lambda * H0 := mul_pos hlambda0 hH0
  have hphysicalHR : lambda * H0 ≤ lambda / 4 := by
    have := mul_le_mul_of_nonneg_left hH0quarter hlambda0.le
    nlinarith
  obtain ⟨J, hJ, hbelow, _habove, j, hj, hadj, _hcomp, _hpole,
      _htransition, hlarge⟩ :=
    hproducer L X k hXL hT0 hscale hpower hphysicalHR hsupport hprimeFree
  have houterPhysical :
      routeTComparableWidthLadder (lambda * H0) (lambda / 4) j ≤ lambda / 4 := by
    rw [routeTComparableWidthLadder, max_le_iff]
    constructor
    · exact hphysicalHR
    · have hpow : (1 : ℝ) ≤ (((2 ^ j : ℕ) : ℝ)) := by
        exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
      have hpowpos : (0 : ℝ) < (((2 ^ j : ℕ) : ℝ)) := by positivity
      exact (div_le_iff₀ hpowpos).2 (by nlinarith)
  have hsupportSelected :
      lambda + 2 * routeTComparableWidthLadder (lambda * H0) (lambda / 4) j ≤ X := by
    linarith
  have hinnerPhysical :
      0 < routeTComparableWidthLadder (lambda * H0) (lambda / 4) (j + 1) :=
    routeTComparableWidthLadder_pos hphysicalH (j + 1)
  have houterPhysicalPos :
      0 < routeTComparableWidthLadder (lambda * H0) (lambda / 4) j :=
    routeTComparableWidthLadder_pos hphysicalH j
  have hbridge :=
    integral_windowRelevant_mul_adjacentNormalizedMellin_eq_physicalSlice
      L X k hXL hT0 hscale hlambda0 hinnerPhysical houterPhysicalPos hadj
        hsupportSelected
  rw [← hbridge] at hlarge
  have hquarter : lambda / 4 = lambda * (1 / 4 : ℝ) := by ring
  have hratio : (lambda / 4) / (lambda * H0) = (1 / 4) / H0 := by
    field_simp
  rw [hratio] at hbelow
  have houterCov :
      routeTComparableWidthLadder (lambda * H0) (lambda / 4) j =
        lambda * routeTComparableWidthLadder H0 (1 / 4) j := by
    rw [hquarter]
    exact routeTComparableWidthLadder_mul_left hlambda0.le j
  have hinnerCov :
      routeTComparableWidthLadder (lambda * H0) (lambda / 4) (j + 1) =
        lambda * routeTComparableWidthLadder H0 (1 / 4) (j + 1) := by
    rw [hquarter]
    exact routeTComparableWidthLadder_mul_left hlambda0.le (j + 1)
  rw [houterCov, hinnerCov] at hlarge
  have hbaseOuter : 0 < routeTComparableWidthLadder H0 (1 / 4) j :=
    routeTComparableWidthLadder_pos hH0 j
  have hbaseInner : 0 < routeTComparableWidthLadder H0 (1 / 4) (j + 1) :=
    routeTComparableWidthLadder_pos hH0 (j + 1)
  have hrecut :=
    integral_windowRelevant_mul_scaled_adjacentNormalizedMellin_eq_leftWindowRelevant
      L X k T0 t hx hlambda (by norm_num : (0 : ℝ) < 1)
        hbaseOuter hbaseInner (by norm_num : (0 : ℝ) < 1)
  have hrecut' :
      (∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t lambda
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
          (routeTNormalizedSmoothWindowMellin lambda
              (lambda * routeTComparableWidthLadder H0 (1 / 4) j)
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin lambda
              (lambda * routeTComparableWidthLadder H0 (1 / 4) (j + 1))
              ((1 : ℂ) + (y : ℝ) * Complex.I))) =
        ∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
              ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin lambda
                (lambda * routeTComparableWidthLadder H0 (1 / 4) j)
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin lambda
                (lambda * routeTComparableWidthLadder H0 (1 / 4) (j + 1))
                ((1 : ℂ) + (y : ℝ) * Complex.I)) := by
    simpa using hrecut
  refine ⟨J, hJ, hbelow, j, hj, ?_⟩
  rw [hrecut'] at hlarge
  simpa using hlarge

end

end RHTower.Sieve

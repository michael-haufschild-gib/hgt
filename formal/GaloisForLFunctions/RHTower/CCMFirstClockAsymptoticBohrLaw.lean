import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewAlmostPeriodic
import GaloisForLFunctions.RHTower.CCMFirstClockTailLowerBoundCompleteness
import GaloisForLFunctions.RHTower.XiLaguerrePolya

/-!
# Asymptotic Bohr law of the literal first CCM clock

After multiplication by aperture, the literal published first-clock coefficient is asymptotic to
twice the critical Xi screw series exactly when RH holds.  The forward direction is a uniform
moving-denominator estimate; the converse uses boundedness of Bohr almost-periodic functions and
the tail-lower-bound completeness theorem.
-/

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HTGeometry

namespace RHTower

noncomputable section

/-- Reciprocal-square weight of the real coordinate of one Xi zero copy. -/
def xiCriticalScrewWeight (q : XiZeroCopy) : ℝ :=
  1 / xiRealSpectralPoint q ^ 2

/-- Relation-hull screw series carried by the real coordinates of all Xi zero copies. -/
def xiCriticalScrewSeries (L : ℝ) : ℝ :=
  screwSeries xiCriticalScrewWeight xiRealSpectralPoint L

/-- Aperture-scaled literal first published CCM clock. -/
def ccmFirstClockScaledPublishedSource (L : ℝ) : ℝ :=
  L * ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L)

/-- Upper endpoint of the RH-side asymptotic relation-hull value interval. -/
def ccmFirstClockAsymptoticHullMax : ℝ :=
  2 * screwHullMax xiCriticalScrewWeight xiRealSpectralPoint

/-- Source-only asymptotic Bohr property.  Its statement contains no zero-location premise. -/
def CCMFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic : Prop :=
  ∃ P : ℝ → ℝ, Continuous P ∧ IsBohrAlmostPeriodic P ∧
    Tendsto (fun L => ccmFirstClockScaledPublishedSource L - P L) atTop (𝓝 0)

theorem xiCriticalScrewWeight_nonneg (q : XiZeroCopy) :
    0 ≤ xiCriticalScrewWeight q := by
  exact one_div_nonneg.mpr (sq_nonneg _)

theorem xiCriticalScrewWeight_pos_of_rh
    (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    0 < xiCriticalScrewWeight q := by
  exact one_div_pos.mpr (sq_pos_of_ne_zero (xiRealSpectralPoint_ne_zero hRH q))

theorem summable_xiCriticalScrewWeight_of_rh (hRH : RiemannHypothesis) :
    Summable xiCriticalScrewWeight := by
  refine xiSpectralPoint_inv_sq_summable.congr (fun q => ?_)
  rw [xiCriticalScrewWeight, xiSpectralPoint_eq_ofReal_of_rh hRH q,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem summable_xiCriticalScrewTerm_of_rh
    (hRH : RiemannHypothesis) (L : ℝ) :
    Summable (fun q : XiZeroCopy =>
      xiCriticalScrewWeight q * (1 - Real.cos (xiRealSpectralPoint q * L))) :=
  summable_screwSeries_term xiCriticalScrewWeight_nonneg
    (summable_xiCriticalScrewWeight_of_rh hRH) L

theorem xiScrewDivisor_re_eq_xiCriticalScrewSeries_of_rh
    (hRH : RiemannHypothesis) (L : ℝ) :
    (xiScrewDivisor L).re = xiCriticalScrewSeries L := by
  rw [xiScrewDivisor, Complex.re_tsum (xiScrewDivisorTerm_summable L)]
  unfold xiCriticalScrewSeries screwSeries
  apply tsum_congr
  intro q
  rw [xiScrewDivisorTerm_eq_ccmFirstClockScrewKernel,
    xiSpectralPoint_eq_ofReal_of_rh hRH q]
  unfold ccmFirstClockScrewKernel xiCriticalScrewWeight
  have hcos : Complex.cos ((L : ℂ) * (xiRealSpectralPoint q : ℂ)) =
      (Real.cos (xiRealSpectralPoint q * L) : ℂ) := by
    rw [show (L : ℂ) * (xiRealSpectralPoint q : ℂ) =
      ((xiRealSpectralPoint q * L : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_cos _).symm
  rw [hcos]
  rw [show (1 : ℂ) - (Real.cos (xiRealSpectralPoint q * L) : ℂ) =
      ((1 - Real.cos (xiRealSpectralPoint q * L) : ℝ) : ℂ) by push_cast; rfl]
  rw [show (xiRealSpectralPoint q : ℂ) ^ 2 =
      ((xiRealSpectralPoint q ^ 2 : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_div]
  simp only [Complex.ofReal_re]
  ring

theorem xiCriticalScrewSeries_continuous_of_rh (hRH : RiemannHypothesis) :
    Continuous xiCriticalScrewSeries :=
  screwSeries_continuous xiCriticalScrewWeight_nonneg
    (summable_xiCriticalScrewWeight_of_rh hRH)

theorem xiCriticalScrewSeries_isBohrAlmostPeriodic_of_rh
    (hRH : RiemannHypothesis) :
    IsBohrAlmostPeriodic xiCriticalScrewSeries :=
  isBohrAlmostPeriodic_screwSeries xiCriticalScrewWeight_nonneg
    (summable_xiCriticalScrewWeight_of_rh hRH)

/-- On RH a first-clock rational summand is the corresponding real moving-denominator term. -/
theorem ccmFirstClockRationalKernel_xiSpectralPoint_re_eq_of_rh
    (hRH : RiemannHypothesis) (L : ℝ) (q : XiZeroCopy) :
    (ccmFirstClockRationalKernel L (xiSpectralPoint q)).re =
      (1 - Real.cos (xiRealSpectralPoint q * L)) /
        (xiRealSpectralPoint q ^ 2 - (2 * Real.pi / L) ^ 2) := by
  rw [xiSpectralPoint_eq_ofReal_of_rh hRH q]
  unfold ccmFirstClockRationalKernel
  have hcos : Complex.cos ((L : ℂ) * (xiRealSpectralPoint q : ℂ)) =
      (Real.cos (xiRealSpectralPoint q * L) : ℂ) := by
    rw [show (L : ℂ) * (xiRealSpectralPoint q : ℂ) =
      ((xiRealSpectralPoint q * L : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_cos _).symm
  rw [hcos]
  rw [show (1 : ℂ) - (Real.cos (xiRealSpectralPoint q * L) : ℂ) =
      ((1 - Real.cos (xiRealSpectralPoint q * L) : ℝ) : ℂ) by push_cast; rfl]
  rw [show (xiRealSpectralPoint q : ℂ) ^ 2 -
        (((2 * Real.pi / L : ℝ) : ℂ)) ^ 2 =
      ((xiRealSpectralPoint q ^ 2 - (2 * Real.pi / L) ^ 2 : ℝ) : ℂ) by
        push_cast; rfl]
  rw [← Complex.ofReal_div]
  exact Complex.ofReal_re _

/-- Sharp uniform error bound for one RH-side first-clock summand. -/
theorem ccmFirstClockRationalKernel_sub_criticalScrewTerm_bounds_of_rh
    (hRH : RiemannHypothesis) {L : ℝ} (hL : 2 * Real.pi ≤ L) (q : XiZeroCopy) :
    0 ≤ (ccmFirstClockRationalKernel L (xiSpectralPoint q)).re -
        xiCriticalScrewWeight q *
          (1 - Real.cos (xiRealSpectralPoint q * L)) ∧
      (ccmFirstClockRationalKernel L (xiSpectralPoint q)).re -
          xiCriticalScrewWeight q *
            (1 - Real.cos (xiRealSpectralPoint q * L)) ≤
        (2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2 * xiCriticalScrewWeight q := by
  let r : ℝ := xiRealSpectralPoint q
  let w : ℝ := 2 * Real.pi / L
  have hLpos : 0 < L := lt_of_lt_of_le (mul_pos (by norm_num) Real.pi_pos) hL
  have hw0 : 0 ≤ w := by dsimp only [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact (div_le_one hLpos).2 hL
  have hr4 : 4 < |r| := by
    have hgap := four_lt_norm_xiSpectralPoint q
    rw [xiSpectralPoint_eq_ofReal_of_rh hRH q, Complex.norm_real,
      Real.norm_eq_abs] at hgap
    exact hgap
  have hr2 : 16 < r ^ 2 := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|r| - 4)]
  have hr2pos : 0 < r ^ 2 := lt_trans (by norm_num) hr2
  have hrne : r ≠ 0 := by nlinarith [sq_nonneg r]
  have hden15 : 15 < r ^ 2 - w ^ 2 := by
    nlinarith [sq_nonneg w]
  have hdenpos : 0 < r ^ 2 - w ^ 2 := lt_trans (by norm_num) hden15
  have hn0 : 0 ≤ 1 - Real.cos (r * L) := sub_nonneg.mpr (Real.cos_le_one _)
  have hn2 : 1 - Real.cos (r * L) ≤ 2 := by
    linarith [Real.neg_one_le_cos (r * L)]
  have hid :
      (1 - Real.cos (r * L)) / (r ^ 2 - w ^ 2) -
          (1 / r ^ 2) * (1 - Real.cos (r * L)) =
        (1 - Real.cos (r * L)) * w ^ 2 /
          (r ^ 2 * (r ^ 2 - w ^ 2)) := by
    field_simp [hrne, ne_of_gt hdenpos]
    ring
  rw [ccmFirstClockRationalKernel_xiSpectralPoint_re_eq_of_rh hRH L q]
  change 0 ≤ (1 - Real.cos (r * L)) / (r ^ 2 - w ^ 2) -
      (1 / r ^ 2) * (1 - Real.cos (r * L)) ∧
    (1 - Real.cos (r * L)) / (r ^ 2 - w ^ 2) -
        (1 / r ^ 2) * (1 - Real.cos (r * L)) ≤
      (2 / 15 : ℝ) * w ^ 2 * (1 / r ^ 2)
  rw [hid]
  constructor
  · positivity
  · calc
      (1 - Real.cos (r * L)) * w ^ 2 / (r ^ 2 * (r ^ 2 - w ^ 2)) =
          (((1 - Real.cos (r * L)) * w ^ 2 / r ^ 2) /
            (r ^ 2 - w ^ 2)) := by
              field_simp [hrne, ne_of_gt hdenpos]
      _ ≤ ((2 * w ^ 2 / r ^ 2) / (r ^ 2 - w ^ 2)) := by
        gcongr
      _ ≤ (2 * w ^ 2 / r ^ 2) / 15 := by
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hden15.le
      _ = (2 / 15 : ℝ) * w ^ 2 * (1 / r ^ 2) := by ring

/-- Difference between the exact first-clock rational divisor and its limiting screw series. -/
def ccmFirstClockMovingDenominatorError (L : ℝ) : ℝ :=
  (ccmFirstClockXiRationalDivisor L).re - xiCriticalScrewSeries L

/-- The full moving-denominator error is nonnegative and uniformly quadratic in the clock
frequency.  Multiplicity is retained by summing over `XiZeroCopy`. -/
theorem ccmFirstClockMovingDenominatorError_bounds_of_rh
    (hRH : RiemannHypothesis) {L : ℝ} (hL : 2 * Real.pi ≤ L) :
    0 ≤ ccmFirstClockMovingDenominatorError L ∧
      ccmFirstClockMovingDenominatorError L ≤
        (2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2 *
          ∑' q : XiZeroCopy, xiCriticalScrewWeight q := by
  have hphysical : Real.pi / 2 ≤ L := by
    have hpi := Real.pi_pos
    linarith
  have hQ := summable_ccmFirstClockRationalKernel_xiSpectralPoint hphysical
  have hQre : Summable (fun q : XiZeroCopy =>
      (ccmFirstClockRationalKernel L (xiSpectralPoint q)).re) :=
    hQ.map Complex.reCLM Complex.reCLM.continuous
  have hS := summable_xiCriticalScrewTerm_of_rh hRH L
  have herr : Summable (fun q : XiZeroCopy =>
      (ccmFirstClockRationalKernel L (xiSpectralPoint q)).re -
        xiCriticalScrewWeight q *
          (1 - Real.cos (xiRealSpectralPoint q * L))) := hQre.sub hS
  have hmajor : Summable (fun q : XiZeroCopy =>
      (2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2 * xiCriticalScrewWeight q) :=
    (summable_xiCriticalScrewWeight_of_rh hRH).mul_left
      ((2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2)
  rw [ccmFirstClockMovingDenominatorError, ccmFirstClockXiRationalDivisor,
    Complex.re_tsum hQ, xiCriticalScrewSeries, screwSeries,
    ← Summable.tsum_sub hQre hS]
  constructor
  · exact tsum_nonneg fun q =>
      (ccmFirstClockRationalKernel_sub_criticalScrewTerm_bounds_of_rh hRH hL q).1
  · calc
      (∑' q : XiZeroCopy,
          ((ccmFirstClockRationalKernel L (xiSpectralPoint q)).re -
            xiCriticalScrewWeight q *
              (1 - Real.cos (xiRealSpectralPoint q * L)))) ≤
          ∑' q : XiZeroCopy,
            ((2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2 *
              xiCriticalScrewWeight q) :=
        herr.tsum_le_tsum
          (fun q =>
            (ccmFirstClockRationalKernel_sub_criticalScrewTerm_bounds_of_rh
              hRH hL q).2) hmajor
      _ = (2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2 *
          ∑' q : XiZeroCopy, xiCriticalScrewWeight q := by
        rw [tsum_mul_left]

/-- The moving-denominator error vanishes quadratically with aperture. -/
theorem ccmFirstClockMovingDenominatorError_tendsto_zero_of_rh
    (hRH : RiemannHypothesis) :
    Tendsto ccmFirstClockMovingDenominatorError atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (2 * Real.pi)] with L hL
    exact (ccmFirstClockMovingDenominatorError_bounds_of_rh hRH hL).1
  · filter_upwards [eventually_ge_atTop (2 * Real.pi)] with L hL
    exact (ccmFirstClockMovingDenominatorError_bounds_of_rh hRH hL).2
  · have hw : Tendsto (fun L : ℝ => 2 * Real.pi / L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hw2 := hw.pow 2
    have hscaled := hw2.const_mul
      ((2 / 15 : ℝ) * ∑' q : XiZeroCopy, xiCriticalScrewWeight q)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- Under RH the scaled literal source converges uniformly at infinity to twice the explicit Xi
screw series. -/
theorem ccmFirstClockScaledSource_sub_explicitScrew_tendsto_zero_of_rh
    (hRH : RiemannHypothesis) :
    Tendsto
      (fun L => ccmFirstClockScaledPublishedSource L - 2 * xiCriticalScrewSeries L)
      atTop (𝓝 0) := by
  have herr : Tendsto (fun L => 2 * ccmFirstClockMovingDenominatorError L) atTop (𝓝 0) := by
    simpa using (ccmFirstClockMovingDenominatorError_tendsto_zero_of_rh hRH).const_mul 2
  have heq :
      (fun L => ccmFirstClockScaledPublishedSource L - 2 * xiCriticalScrewSeries L) =ᶠ[atTop]
        (fun L => 2 * ccmFirstClockMovingDenominatorError L) := by
    filter_upwards [eventually_ge_atTop (2 * Real.pi)] with L hL
    have hphysical : Real.pi / 2 ≤ L := by
      have hpi := Real.pi_pos
      linarith
    have hLne : L ≠ 0 := by
      have hpi := Real.pi_pos
      linarith
    rw [ccmFirstClockScaledPublishedSource,
      ccmPublishedSourceSineCoefficient_firstClock_eq_xiRationalDivisor hphysical,
      ccmFirstClockMovingDenominatorError]
    field_simp [hLne]
  exact herr.congr' heq.symm

theorem ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic_of_rh
    (hRH : RiemannHypothesis) :
    CCMFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic := by
  refine ⟨(fun L => 2 * xiCriticalScrewSeries L), ?_, ?_, ?_⟩
  · exact continuous_const.mul (xiCriticalScrewSeries_continuous_of_rh hRH)
  · have hcont := xiCriticalScrewSeries_continuous_of_rh hRH
    have hap := xiCriticalScrewSeries_isBohrAlmostPeriodic_of_rh hRH
    have hadd := isBohrAlmostPeriodic_add hcont hap hcont hap
    simpa only [two_mul] using hadd
  · exact ccmFirstClockScaledSource_sub_explicitScrew_tendsto_zero_of_rh hRH

/-- Any asymptotic Bohr model forces a fixed lower floor for the literal first clock, hence RH. -/
theorem riemannHypothesis_of_ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic
    (hABP : CCMFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic) :
    RiemannHypothesis := by
  obtain ⟨P, hPcont, hPap, hlimit⟩ := hABP
  obtain ⟨C, hC⟩ := exists_bound_of_isBohrAlmostPeriodic hPcont hPap
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (P 0)) (hC 0)
  obtain ⟨A, hA⟩ := (Metric.tendsto_atTop.mp hlimit) 1 one_pos
  let T : ℝ := max (max A 1) (Real.pi / 2)
  have hTphysical : Real.pi / 2 ≤ T := le_max_right _ _
  apply riemannHypothesis_of_ccmFirstClockPublishedSourceEventuallyBoundedBelow
  refine ⟨C + 1, T, by linarith, hTphysical, ?_⟩
  intro L hTL
  have hLA : A ≤ L := le_trans (le_trans (le_max_left A 1) (le_max_left _ _)) hTL
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right A 1) (le_max_left _ _)) hTL
  have hsmall := hA L hLA
  rw [Real.dist_eq, sub_zero, abs_lt] at hsmall
  have hPbelow : -C ≤ P L := by
    have habs := hC L
    rw [Real.norm_eq_abs, abs_le] at habs
    exact habs.1
  have hscaledBelow : -(C + 1) ≤ ccmFirstClockScaledPublishedSource L := by
    linarith [hsmall.1]
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hdiv : -(C + 1) / L ≤
      ccmFirstClockScaledPublishedSource L / L :=
    div_le_div_of_nonneg_right hscaledBelow hLpos.le
  have hself : (C + 1) / L ≤ C + 1 := div_le_self (by linarith) hL1
  have hsource :
      ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) =
        ccmFirstClockScaledPublishedSource L / L := by
    rw [ccmFirstClockScaledPublishedSource]
    field_simp [hLpos.ne']
  rw [hsource]
  calc
    -(C + 1) ≤ -((C + 1) / L) := neg_le_neg hself
    _ = -(C + 1) / L := by ring
    _ ≤ ccmFirstClockScaledPublishedSource L / L := hdiv

/-- **Exact source-only criterion.** The scaled literal first CCM clock is asymptotically Bohr
almost periodic exactly when RH holds. -/
theorem ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic_iff_rh :
    CCMFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic,
    ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic_of_rh⟩

/-- Every point of the full relation-hull interval is approximated by the scaled literal source
with bounded gaps after one threshold.  No simplicity or rational-independence premise is used. -/
theorem exists_eventual_window_ccmFirstClockScaledPublishedSource_near_of_rh
    (hRH : RiemannHypothesis) {y : ℝ}
    (hy : y ∈ Set.Icc 0 ccmFirstClockAsymptoticHullMax)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : ℝ, 0 < W ∧ ∃ T : ℝ, ∀ tau : ℝ, T ≤ tau →
      ∃ t ∈ Set.Icc tau (tau + W),
        |ccmFirstClockScaledPublishedSource t - y| < ε := by
  have hsum := summable_xiCriticalScrewWeight_of_rh hRH
  have hmax0 : 0 ≤ screwHullMax xiCriticalScrewWeight xiRealSpectralPoint :=
    screwHullMax_nonneg xiCriticalScrewWeight_nonneg hsum
  have hyhalf : y / 2 ∈
      Set.Icc 0 (screwHullMax xiCriticalScrewWeight xiRealSpectralPoint) := by
    rw [ccmFirstClockAsymptoticHullMax] at hy
    constructor <;> linarith [hy.1, hy.2]
  obtain ⟨W, hW, hwindow⟩ :=
    exists_window_screwSeries_near xiCriticalScrewWeight_nonneg hsum
      hyhalf (by linarith : 0 < ε / 4)
  have hlimit := ccmFirstClockScaledSource_sub_explicitScrew_tendsto_zero_of_rh hRH
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp hlimit) (ε / 2) (by linarith)
  refine ⟨W, hW, T, ?_⟩
  intro tau htau
  obtain ⟨t, ht, hseries⟩ := hwindow tau
  refine ⟨t, ht, ?_⟩
  have hpert := hT t (htau.trans ht.1)
  rw [Real.dist_eq, sub_zero] at hpert
  have hseries2 : |2 * xiCriticalScrewSeries t - y| < ε / 2 := by
    change |xiCriticalScrewSeries t - y / 2| < ε / 4 at hseries
    rw [show 2 * xiCriticalScrewSeries t - y =
      2 * (xiCriticalScrewSeries t - y / 2) by ring, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |xiCriticalScrewSeries t - y / 2| < 2 * (ε / 4) :=
        mul_lt_mul_of_pos_left hseries (by norm_num)
      _ = ε / 2 := by ring
  calc
    |ccmFirstClockScaledPublishedSource t - y| =
        |(ccmFirstClockScaledPublishedSource t - 2 * xiCriticalScrewSeries t) +
          (2 * xiCriticalScrewSeries t - y)| := by ring_nf
    _ ≤ |ccmFirstClockScaledPublishedSource t - 2 * xiCriticalScrewSeries t| +
        |2 * xiCriticalScrewSeries t - y| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hpert hseries2
    _ = ε := by ring

/-- Exact replacement for rational independence: the asymptotic absolute endpoint is reached by
the relation hull exactly when every finite integral frequency relation has even coefficient sum. -/
theorem ccmFirstClockAsymptoticHullMax_eq_absoluteBound_iff_parity_of_rh
    (hRH : RiemannHypothesis) :
    ccmFirstClockAsymptoticHullMax =
        4 * ∑' q : XiZeroCopy, xiCriticalScrewWeight q ↔
      ∀ n : XiZeroCopy →₀ ℤ,
        n ∈ screwRelationLattice xiRealSpectralPoint → Even (n.sum fun _ m => m) := by
  have hsum := summable_xiCriticalScrewWeight_of_rh hRH
  have hbase := screwHullMax_eq_two_mul_tsum_iff
    (omega := xiRealSpectralPoint)
    (fun q => xiCriticalScrewWeight_pos_of_rh hRH q) hsum
  rw [ccmFirstClockAsymptoticHullMax]
  constructor
  · intro h
    apply hbase.mp
    linarith
  · intro h
    have hmax := hbase.mpr h
    linarith

end

end RHTower

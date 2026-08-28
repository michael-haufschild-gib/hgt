import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeArithmeticCofinalContour

/-!
# Cofinal corrected-prime contour schedule invariance

This module proves that contour choice has no asymptotic freedom once rectangles are admissible,
cross the centered archimedean pole, and cofinally exhaust finite Xi-divisor packets.  Every such
corrected literal prime-contour schedule converges to the same complete physical Weil energy; every
raw schedule converges to that energy minus the same explicit square.  Hence differences between
any two schedules tend to zero.

The consequence is a schedule-selection no-go.  Sharp asymptotic nonnegativity along each, some,
or all cofinal schedules is equivalent to RH.  Under failure of RH, every cofinal schedule has one
physical logarithmic sample that is eventually bounded above by a strictly negative floor.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- A cofinal pole-crossing admissible rectangle schedule. -/
structure XiPhysicalThetaAbelEnergyPrimeCofinalSchedule where
  lower : ℕ → ℂ
  upper : ℕ → ℂ
  re_lt : ∀ m, (lower m).re < (upper m).re
  im_lt : ∀ m, (lower m).im < (upper m).im
  left_neg : ∀ m, (lower m).re < 0
  right_pos : ∀ m, 0 < (upper m).re
  below_pole : ∀ m, (lower m).im < -(1 / 2)
  above_pole : ∀ m, -(1 / 2) < (upper m).im
  top_lt : ∀ m, (upper m).im < 1 / 2
  bottom_admissible : ∀ m, ∀ x ∈ uIcc (lower m).re (upper m).re,
    XiExplicitAdmissible ((x : ℂ) + (lower m).im * I)
  top_admissible : ∀ m, ∀ x ∈ uIcc (lower m).re (upper m).re,
    XiExplicitAdmissible ((x : ℂ) + (upper m).im * I)
  right_admissible : ∀ m, ∀ y ∈ uIcc (lower m).im (upper m).im,
    XiExplicitAdmissible (((upper m).re : ℂ) + y * I)
  left_admissible : ∀ m, ∀ y ∈ uIcc (lower m).im (upper m).im,
    XiExplicitAdmissible (((lower m).re : ℂ) + y * I)
  cofinal : ∀ t : Finset XiZeroCopy, ∀ᶠ m : ℕ in atTop,
    t ≤ xiZeroCopyClosedRectangle (lower m) (upper m)

/-- The least-coded arithmetic rectangles form a cofinal prime-contour schedule. -/
noncomputable def xiPhysicalThetaAbelEnergyArithmeticPrimeCofinalSchedule :
    XiPhysicalThetaAbelEnergyPrimeCofinalSchedule where
  lower := xiPhysicalThetaAbelEnergyArithmeticLower
  upper := xiPhysicalThetaAbelEnergyArithmeticUpper
  re_lt m := (xiPhysicalThetaAbelEnergyArithmetic_poleCrossing_geometry m).1
  im_lt m := (xiPhysicalThetaAbelEnergyArithmetic_poleCrossing_geometry m).2.1
  left_neg m := (xiPhysicalThetaAbelEnergyArithmetic_poleCrossing_geometry m).2.2.1
  right_pos m := (xiPhysicalThetaAbelEnergyArithmetic_poleCrossing_geometry m).2.2.2.1
  below_pole m := (xiPhysicalThetaAbelEnergyArithmetic_poleCrossing_geometry m).2.2.2.2.1
  above_pole m := (xiPhysicalThetaAbelEnergyArithmetic_poleCrossing_geometry m).2.2.2.2.2.1
  top_lt m := (xiPhysicalThetaAbelEnergyArithmetic_poleCrossing_geometry m).2.2.2.2.2.2
  bottom_admissible m := (xiPhysicalThetaAbelEnergyArithmetic_admissible m).1
  top_admissible m := (xiPhysicalThetaAbelEnergyArithmetic_admissible m).2.1
  right_admissible m := (xiPhysicalThetaAbelEnergyArithmetic_admissible m).2.2.1
  left_admissible m := (xiPhysicalThetaAbelEnergyArithmetic_admissible m).2.2.2
  cofinal := eventually_finset_subset_xiPhysicalThetaAbelEnergyArithmeticRectangle

/-- Corrected direct-prime sample along an arbitrary cofinal schedule. -/
def XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.correctedPrimeSample
    (S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    (L A c a : ℝ) (m : ℕ) : ℂ :=
  xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour L A c a
    (S.lower m) (S.upper m)

/-- Raw direct-prime sample along an arbitrary cofinal schedule. -/
def XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.primeSample
    (S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    (L A c a : ℝ) (m : ℕ) : ℂ :=
  xiPhysicalThetaAbelEnergyNormalizedPrimeSourceContour L A c a
    (S.lower m) (S.upper m)

theorem XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.correctedPrimeSample_eq_zeroSum
    (S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    (L A c a : ℝ) (m : ℕ) :
    S.correctedPrimeSample L A c a m =
      ∑ q ∈ xiZeroCopyClosedRectangle (S.lower m) (S.upper m),
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
          (xiSpectralPoint q) ^ 2 := by
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd L A c a)
      (S.re_lt m) (S.im_lt m) (S.bottom_admissible m) (S.top_admissible m)
      (S.right_admissible m) (S.left_admissible m)
  have hC : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.correctedPrimeSample,
    ← xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_correctedPrime
      (S.bottom_admissible m) (S.top_admissible m)
      (S.right_admissible m) (S.left_admissible m)
      (S.im_lt m) (S.left_neg m) (S.right_pos m)
      (S.below_pole m) (S.above_pole m) (S.top_lt m),
    xiPhysicalThetaAbelEnergyNormalizedSourceContour, hcontour,
    ← mul_assoc, inv_mul_cancel₀ hC, one_mul]

/-- Every cofinal corrected-prime schedule converges to complete physical Weil energy. -/
theorem XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.tendsto_correctedPrimeSample_weil
    (S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    Tendsto (fun m : ℕ => S.correctedPrimeSample L A c a m) atTop
      (𝓝 (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a))) := by
  let f : XiZeroCopy → ℂ := fun q =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
      (xiSpectralPoint q) ^ 2
  have hsum : Summable f :=
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_summable hA hc L a
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hball : Metric.ball (∑' q, f q) ε ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hε
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) ε :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨t, ht⟩ := hevent
  filter_upwards [S.cofinal t] with m hm
  have hnear := ht (xiZeroCopyClosedRectangle (S.lower m) (S.upper m)) hm
  rw [Metric.mem_ball] at hnear
  rw [S.correctedPrimeSample_eq_zeroSum]
  simpa [f, xiWeilPolarization_physicalThetaAbelEnergy_eq_tsum_sq] using hnear

/-- Every cofinal raw-prime schedule has the same Weil-minus-archimedean-square limit. -/
theorem XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.tendsto_primeSample_weil_sub_archSq
    (S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    Tendsto (fun m : ℕ => S.primeSample L A c a m) atTop
      (𝓝 (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a) -
        (((Real.exp (a / 2) * 2 * (1 - Real.exp (-(L / 2))) * c * A : ℝ) : ℂ) ^ 2))) := by
  have h := S.tendsto_correctedPrimeSample_weil hA hc L a
  let K : ℂ :=
    (((Real.exp (a / 2) * 2 * (1 - Real.exp (-(L / 2))) * c * A : ℝ) : ℂ) ^ 2)
  have hconst : Tendsto (fun _ : ℕ => K) atTop (𝓝 K) := tendsto_const_nhds
  have hsub := h.sub hconst
  dsimp only [K] at hsub
  simpa [XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.correctedPrimeSample,
    XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.primeSample,
    xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour] using hsub

/-- Any two cofinal corrected-prime schedules are asymptotically indistinguishable. -/
theorem tendsto_correctedPrimeSample_sub_schedule_zero
    (S T : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    Tendsto (fun m : ℕ =>
      S.correctedPrimeSample L A c a m -
        T.correctedPrimeSample L A c a m) atTop (𝓝 0) := by
  have hS := S.tendsto_correctedPrimeSample_weil hA hc L a
  have hT := T.tendsto_correctedPrimeSample_weil hA hc L a
  simpa using hS.sub hT

/-- Any two cofinal raw-prime schedules are asymptotically indistinguishable. -/
theorem tendsto_primeSample_sub_schedule_zero
    (S T : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    Tendsto (fun m : ℕ =>
      S.primeSample L A c a m - T.primeSample L A c a m) atTop (𝓝 0) := by
  have hS := S.tendsto_primeSample_weil_sub_archSq hA hc L a
  have hT := T.tendsto_primeSample_weil_sub_archSq hA hc L a
  simpa using hS.sub hT

/-- Sharp zero-floor condition along one arbitrary cofinal prime-contour schedule. -/
def XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.AsymptoticallyNonnegative
    (S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    (L A c : ℝ) : Prop :=
  ∀ n : ℕ, L < Real.log n / 2 → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ m : ℕ in atTop,
      -ε < (S.correctedPrimeSample L A c (Real.log n / 2) m).re

theorem XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.asymptoticallyNonnegative_iff_rh
    (S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    S.AsymptoticallyNonnegative L A c ↔ RiemannHypothesis := by
  constructor
  · intro hasym
    rw [riemannHypothesis_iff_physicalThetaAbelEnergy_logSample_weil_nonneg
      hL hA hc]
    intro n hLn
    let W : ℂ := xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
    have hrelim : Tendsto
        (fun m : ℕ =>
          (S.correctedPrimeSample L A c (Real.log n / 2) m).re) atTop (𝓝 W.re) :=
      (Complex.continuous_re.tendsto _).comp
        (S.tendsto_correctedPrimeSample_weil hA hc L (Real.log n / 2))
    by_contra hW
    have hWneg : W.re < 0 := lt_of_not_ge hW
    let ε : ℝ := -W.re / 2
    have hε : 0 < ε := by dsimp only [ε]; linarith
    have hlower := hasym n hLn ε hε
    have hupper : ∀ᶠ m : ℕ in atTop,
        (S.correctedPrimeSample L A c (Real.log n / 2) m).re < -ε := by
      exact hrelim.eventually (Iio_mem_nhds (by
        dsimp only [ε]
        linarith))
    obtain ⟨m, hmLower, hmUpper⟩ := (hlower.and hupper).exists
    linarith
  · intro hRH n _hLn ε hε
    let W : ℂ := xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
    have hweil : 0 ≤ W.re :=
      (riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform_squareSummable
          hA hc L (Real.log n / 2))
    have hrelim : Tendsto
        (fun m : ℕ =>
          (S.correctedPrimeSample L A c (Real.log n / 2) m).re) atTop (𝓝 W.re) :=
      (Complex.continuous_re.tendsto _).comp
        (S.tendsto_correctedPrimeSample_weil hA hc L (Real.log n / 2))
    exact hrelim.eventually
      (Ioi_mem_nhds (lt_of_lt_of_le (neg_lt_zero.mpr hε) hweil))

/-- False-RH witness on a schedule: one physical log sample is eventually uniformly negative. -/
def XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.EventuallyNegativeWitness
    (S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    (L A c : ℝ) : Prop :=
  ∃ n : ℕ, L < Real.log n / 2 ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ m : ℕ in atTop,
      (S.correctedPrimeSample L A c (Real.log n / 2) m).re < -δ

theorem XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.eventuallyNegativeWitness_iff_not_rh
    (S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule)
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    S.EventuallyNegativeWitness L A c ↔ ¬RiemannHypothesis := by
  constructor
  · rintro ⟨n, hLn, δ, hδ, hupper⟩ hRH
    have hlower :=
      (S.asymptoticallyNonnegative_iff_rh hL hA hc).2 hRH n hLn δ hδ
    obtain ⟨m, hmLower, hmUpper⟩ := (hlower.and hupper).exists
    linarith
  · intro hnotRH
    have hnot : ¬ ∀ n : ℕ, L < Real.log n / 2 →
        0 ≤ (xiWeilPolarization
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
            (Real.log n / 2))).re := by
      intro hall
      apply hnotRH
      exact (riemannHypothesis_iff_physicalThetaAbelEnergy_logSample_weil_nonneg
        hL hA hc).2 hall
    simp only [not_forall, not_le] at hnot
    obtain ⟨n, hLn, hWneg⟩ := hnot
    let W : ℂ := xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
    let δ : ℝ := -W.re / 2
    have hδ : 0 < δ := by dsimp only [δ, W]; linarith
    have hrelim : Tendsto
        (fun m : ℕ =>
          (S.correctedPrimeSample L A c (Real.log n / 2) m).re) atTop (𝓝 W.re) :=
      (Complex.continuous_re.tendsto _).comp
        (S.tendsto_correctedPrimeSample_weil hA hc L (Real.log n / 2))
    refine ⟨n, hLn, δ, hδ, ?_⟩
    exact hrelim.eventually (Iio_mem_nhds (by
      dsimp only [δ, W]
      linarith))

/-- Every cofinal schedule passes the sharp zero-floor test exactly under RH. -/
theorem all_primeCofinalSchedules_asymptoticallyNonnegative_iff_rh
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    (∀ S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule,
      S.AsymptoticallyNonnegative L A c) ↔ RiemannHypothesis := by
  constructor
  · intro hall
    exact (xiPhysicalThetaAbelEnergyArithmeticPrimeCofinalSchedule
      |>.asymptoticallyNonnegative_iff_rh hL hA hc).1
        (hall xiPhysicalThetaAbelEnergyArithmeticPrimeCofinalSchedule)
  · intro hRH S
    exact (S.asymptoticallyNonnegative_iff_rh hL hA hc).2 hRH

/-- Under false RH every cofinal schedule has an eventually negative physical sample. -/
theorem all_primeCofinalSchedules_eventuallyNegativeWitness_iff_not_rh
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    (∀ S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule,
      S.EventuallyNegativeWitness L A c) ↔ ¬RiemannHypothesis := by
  constructor
  · intro hall
    exact (xiPhysicalThetaAbelEnergyArithmeticPrimeCofinalSchedule
      |>.eventuallyNegativeWitness_iff_not_rh hL hA hc).1
        (hall xiPhysicalThetaAbelEnergyArithmeticPrimeCofinalSchedule)
  · intro hnot S
    exact (S.eventuallyNegativeWitness_iff_not_rh hL hA hc).2 hnot

theorem unitAllPrimeCofinalSchedulesAsymptoticallyNonnegative_iff_rh :
    (∀ S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule,
      S.AsymptoticallyNonnegative 1 1 1) ↔ RiemannHypothesis := by
  exact all_primeCofinalSchedules_asymptoticallyNonnegative_iff_rh
    (by norm_num) (by norm_num) (by norm_num)

/-- Closed false-RH form: every cofinal schedule eventually enters a strict negative chamber. -/
theorem unitAllPrimeCofinalSchedulesEventuallyNegativeWitness_iff_not_rh :
    (∀ S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule,
      S.EventuallyNegativeWitness 1 1 1) ↔ ¬RiemannHypothesis := by
  exact all_primeCofinalSchedules_eventuallyNegativeWitness_iff_not_rh
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower

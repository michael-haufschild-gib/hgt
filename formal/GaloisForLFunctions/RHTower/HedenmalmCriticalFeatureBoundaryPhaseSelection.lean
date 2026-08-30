import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureTranslatedPhaseFiniteSourceDecomposition

/-!
# Boundary-first source phase selection for HCF

Finite-displacement phase selection chooses the phase after the displacement.  That order leaves a
moving-phase Plemelj problem.  Here the order is reversed: first take the compact source boundary
functional, choose a phase from its exact zero Fourier mode, and only then shrink a positive
displacement at that fixed phase.

Every selected object below is defined from `XiC` boundary or pole--Gamma source evaluations.  A
finite real-zero expansion is used only to prove the zero-mean law; it is not part of the selected
phase.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open RHTower.RealBoundaryDivisor
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-- Smooth compact test obtained by translating the complete HCF periodization. -/
def criticalFeatureFullBoundaryCutoffWeight
    (theta : ℝ) (cutoff : ℕ) (x : ℝ) : ℝ :=
  criticalFeatureRealBoundaryPeriodization (x + theta) *
    SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) x

/-- Smooth compact zero Fourier mode of the translated HCF test. -/
def criticalFeatureZeroModeBoundaryCutoffWeight
    (cutoff : ℕ) (x : ℝ) : ℝ :=
  2 * Real.pi * SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) x

theorem continuous_criticalFeatureFullBoundaryCutoffWeight
    (theta : ℝ) (cutoff : ℕ) :
    Continuous (criticalFeatureFullBoundaryCutoffWeight theta cutoff) := by
  unfold criticalFeatureFullBoundaryCutoffWeight
  exact (continuous_criticalFeatureRealBoundaryPeriodization.comp
      (continuous_id.add continuous_const)).mul
    (SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ)).continuous

theorem continuous_criticalFeatureZeroModeBoundaryCutoffWeight
    (cutoff : ℕ) :
    Continuous (criticalFeatureZeroModeBoundaryCutoffWeight cutoff) := by
  unfold criticalFeatureZeroModeBoundaryCutoffWeight
  exact continuous_const.mul
    (SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ)).continuous

theorem criticalFeatureFullBoundaryCutoffWeight_eq_zero_of_not_mem
    (theta : ℝ) (cutoff : ℕ) {x : ℝ}
    (hx : x ∉ Ioo (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3)) :
    criticalFeatureFullBoundaryCutoffWeight theta cutoff x = 0 := by
  unfold criticalFeatureFullBoundaryCutoffWeight
  have hnot : x ∉ tsupport (SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ)) := by
    rw [SchwartzMap.realCompactIntervalCutoff_tsupport]
    have hn : (0 : ℝ) ≤ (cutoff : ℝ) := by positivity
    rw [abs_of_nonneg hn]
    simp only [Set.mem_setOf_eq]
    intro hle
    apply hx
    constructor
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x]
  rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]

theorem criticalFeatureZeroModeBoundaryCutoffWeight_eq_zero_of_not_mem
    (cutoff : ℕ) {x : ℝ}
    (hx : x ∉ Ioo (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3)) :
    criticalFeatureZeroModeBoundaryCutoffWeight cutoff x = 0 := by
  unfold criticalFeatureZeroModeBoundaryCutoffWeight
  have hnot : x ∉ tsupport (SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ)) := by
    rw [SchwartzMap.realCompactIntervalCutoff_tsupport]
    have hn : (0 : ℝ) ≤ (cutoff : ℝ) := by positivity
    rw [abs_of_nonneg hn]
    simp only [Set.mem_setOf_eq]
    intro hle
    apply hx
    constructor
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x]
  rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]

/-- Complete translated compact boundary observable, before divisor scalarization. -/
def criticalFeatureCompactFullBoundaryObservableAtPhase
    (theta : ℝ) (cutoff : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
    criticalFeatureFullBoundaryCutoffWeight theta cutoff x * boundaryDensity XiC eta x

/-- Compact zero-mode boundary observable. -/
def criticalFeatureCompactZeroModeBoundaryObservable
    (cutoff : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
    criticalFeatureZeroModeBoundaryCutoffWeight cutoff x * boundaryDensity XiC eta x

/-- Boundary-selected full-periodization value.  Definition contains no zero index. -/
def criticalFeatureCompactFullSourceBoundaryLimitAtPhase
    (cutoff : ℕ) (theta : ℝ) : ℝ :=
  limUnder (nhdsWithin (0 : ℝ) (Ioi 0))
    (criticalFeatureCompactFullBoundaryObservableAtPhase theta cutoff)

/-- Boundary-selected zero Fourier mode.  Definition contains no zero index. -/
def criticalFeatureCompactZeroModeSourceBoundaryLimit (cutoff : ℕ) : ℝ :=
  limUnder (nhdsWithin (0 : ℝ) (Ioi 0))
    (criticalFeatureCompactZeroModeBoundaryObservable cutoff)

/-- Boundary source alias whose sign chooses the phase before displacement. -/
def criticalFeatureCompactSourceBoundaryAliasAtPhase
    (cutoff : ℕ) (theta : ℝ) : ℝ :=
  criticalFeatureCompactFullSourceBoundaryLimitAtPhase cutoff theta -
    criticalFeatureCompactZeroModeSourceBoundaryLimit cutoff

/-- One finite real-zero packet represents every phase of the compact source boundary family.
The packet is produced by the boundary theorem and is not present in any source definition. -/
theorem exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums
    (cutoff : ℕ) :
    ∃ Gamma : Finset ℝ,
      (∀ gamma : ℝ, gamma ∈ Gamma ↔
        ((gamma : ℂ) ∈ Metric.ball (0 : ℂ) ((cutoff : ℝ) + 4) ∧
          XiC (gamma : ℂ) = 0)) ∧
      criticalFeatureCompactZeroModeSourceBoundaryLimit cutoff =
        ∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureZeroModeBoundaryCutoffWeight cutoff gamma ∧
      ∀ theta : ℝ,
        criticalFeatureCompactFullSourceBoundaryLimitAtPhase cutoff theta =
          ∑ gamma ∈ Gamma,
            ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
              criticalFeatureFullBoundaryCutoffWeight theta cutoff gamma := by
  have hr : 0 ≤ (cutoff : ℝ) + 3 := by positivity
  have hrR : (cutoff : ℝ) + 3 < (cutoff : ℝ) + 4 := by linarith
  obtain ⟨Gamma, hGamma, hzeroLim⟩ :=
    XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral
      (c := 0) (r := (cutoff : ℝ) + 3) (R := (cutoff : ℝ) + 4)
      hr hrR
      (continuous_criticalFeatureZeroModeBoundaryCutoffWeight cutoff)
      (fun x hx => by
        apply criticalFeatureZeroModeBoundaryCutoffWeight_eq_zero_of_not_mem cutoff
        simpa only [zero_sub, zero_add] using hx)
  refine ⟨Gamma, by simpa using hGamma, ?_, ?_⟩
  · rw [criticalFeatureCompactZeroModeSourceBoundaryLimit]
    change limUnder (nhdsWithin (0 : ℝ) (Ioi 0))
      (fun eta : ℝ =>
        ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
          criticalFeatureZeroModeBoundaryCutoffWeight cutoff x *
            boundaryDensity XiC eta x) = _
    simpa only [zero_sub, zero_add] using hzeroLim.limUnder_eq
  · intro theta
    obtain ⟨GammaTheta, hGammaTheta, hfullLim⟩ :=
      XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral
        (c := 0) (r := (cutoff : ℝ) + 3) (R := (cutoff : ℝ) + 4)
        hr hrR
        (continuous_criticalFeatureFullBoundaryCutoffWeight theta cutoff)
        (fun x hx => by
          apply criticalFeatureFullBoundaryCutoffWeight_eq_zero_of_not_mem theta cutoff
          simpa only [zero_sub, zero_add] using hx)
    have hsame : GammaTheta = Gamma := by
      ext gamma
      rw [hGammaTheta, hGamma]
    rw [criticalFeatureCompactFullSourceBoundaryLimitAtPhase]
    change limUnder (nhdsWithin (0 : ℝ) (Ioi 0))
      (fun eta : ℝ =>
        ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
          criticalFeatureFullBoundaryCutoffWeight theta cutoff x *
            boundaryDensity XiC eta x) = _
    rw [← hsame]
    simpa only [zero_sub, zero_add] using hfullLim.limUnder_eq

/-- The boundary alias is a finite continuous phase reporter. -/
theorem continuous_criticalFeatureCompactSourceBoundaryAliasAtPhase
    (cutoff : ℕ) :
    Continuous (criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff) := by
  obtain ⟨Gamma, _hGamma, hzero, hfull⟩ :=
    exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums cutoff
  have hformula : criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff =
      fun theta : ℝ =>
        ∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            (criticalFeatureFullBoundaryCutoffWeight theta cutoff gamma -
              criticalFeatureZeroModeBoundaryCutoffWeight cutoff gamma) := by
    funext theta
    rw [criticalFeatureCompactSourceBoundaryAliasAtPhase, hfull theta, hzero]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro gamma hgamma
    ring
  rw [hformula]
  apply continuous_finsetSum Gamma
  intro gamma hgamma
  unfold criticalFeatureFullBoundaryCutoffWeight
    criticalFeatureZeroModeBoundaryCutoffWeight
  exact continuous_const.mul
    (((continuous_criticalFeatureRealBoundaryPeriodization.comp
        (continuous_const.add continuous_id)).mul continuous_const).sub continuous_const)

private theorem exists_ge_zero_of_intervalIntegral_eq_zero
    {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : (∫ x in (0 : ℝ)..1, f x) = 0) :
    ∃ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x := by
  have hnonempty : (Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr (by norm_num)
  obtain ⟨x, hxmem, hxmax⟩ :=
    isCompact_Icc.exists_isMaxOn hnonempty hf.continuousOn
  refine ⟨x, hxmem, ?_⟩
  have hmono :
      (∫ t in (0 : ℝ)..1, f t) ≤ ∫ _t in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_mono_on (by norm_num)
      (hf.intervalIntegrable _ _) intervalIntegrable_const
      (fun t ht => hxmax ht)
  rw [hzero] at hmono
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono

/-- Haar-cell averaging survives the Plemelj boundary limit exactly.  This is proved after the
source limit has been fixed, so no moving-phase interchange is used. -/
theorem intervalIntegral_criticalFeatureCompactSourceBoundaryAliasAtPhase_eq_zero
    (cutoff : ℕ) :
    (∫ theta in (0 : ℝ)..1,
      criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta) = 0 := by
  obtain ⟨Gamma, _hGamma, hzero, hfull⟩ :=
    exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums cutoff
  have hformula (theta : ℝ) :
      criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta =
        ∑ gamma ∈ Gamma,
          (((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma) *
              (criticalFeatureRealBoundaryPeriodization (gamma + theta) - 2 * Real.pi) := by
    rw [criticalFeatureCompactSourceBoundaryAliasAtPhase, hfull theta, hzero]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro gamma hgamma
    unfold criticalFeatureFullBoundaryCutoffWeight
      criticalFeatureZeroModeBoundaryCutoffWeight
    ring
  have hcell (gamma : ℝ) :
      (∫ theta in (0 : ℝ)..1,
        (criticalFeatureRealBoundaryPeriodization (gamma + theta) - 2 * Real.pi)) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact integral_Ioc_criticalFeatureRealBoundaryPeriodization_add_sub_two_pi_eq_zero gamma
  calc
    (∫ theta in (0 : ℝ)..1,
        criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta) =
        ∫ theta in (0 : ℝ)..1,
          ∑ gamma ∈ Gamma,
            (((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
              SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma) *
                (criticalFeatureRealBoundaryPeriodization (gamma + theta) - 2 * Real.pi) := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      exact hformula theta
    _ = ∑ gamma ∈ Gamma,
          ∫ theta in (0 : ℝ)..1,
            (((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
              SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma) *
                (criticalFeatureRealBoundaryPeriodization (gamma + theta) - 2 * Real.pi) := by
      rw [intervalIntegral.integral_finsetSum]
      intro gamma hgamma
      exact (continuous_const.mul
        ((continuous_criticalFeatureRealBoundaryPeriodization.comp
          (continuous_const.add continuous_id)).sub continuous_const)).intervalIntegrable _ _
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro gamma hgamma
      rw [intervalIntegral.integral_const_mul, hcell gamma, mul_zero]

/-- A phase is selected from the source boundary functional before any positive displacement is
chosen. -/
theorem exists_criticalFeatureCompactBoundaryDealiasingPhase
    (cutoff : ℕ) :
    ∃ theta ∈ Icc (0 : ℝ) 1,
      0 ≤ criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta := by
  exact exists_ge_zero_of_intervalIntegral_eq_zero
    (continuous_criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff)
    (intervalIntegral_criticalFeatureCompactSourceBoundaryAliasAtPhase_eq_zero cutoff)

/-- Canonical boundary-first source phase. -/
def criticalFeatureCompactBoundaryDealiasingPhase (cutoff : ℕ) : ℝ :=
  Classical.choose (exists_criticalFeatureCompactBoundaryDealiasingPhase cutoff)

theorem criticalFeatureCompactBoundaryDealiasingPhase_mem (cutoff : ℕ) :
    criticalFeatureCompactBoundaryDealiasingPhase cutoff ∈ Icc (0 : ℝ) 1 :=
  (Classical.choose_spec
    (exists_criticalFeatureCompactBoundaryDealiasingPhase cutoff)).1

theorem criticalFeatureCompactBoundaryDealiasingPhase_spec (cutoff : ℕ) :
    0 ≤ criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff
      (criticalFeatureCompactBoundaryDealiasingPhase cutoff) :=
  (Classical.choose_spec
    (exists_criticalFeatureCompactBoundaryDealiasingPhase cutoff)).2

/-- Pole--Gamma realization of the complete compact phase observable. -/
def criticalFeatureCompactFullPoleGammaObservableAtPhase
    (theta : ℝ) (cutoff : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
    criticalFeatureFullBoundaryCutoffWeight theta cutoff x *
      criticalFeaturePositiveShiftPoleGammaDensity eta x

/-- Pole--Gamma realization of the compact zero mode. -/
def criticalFeatureCompactZeroModePoleGammaObservable
    (cutoff : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
    criticalFeatureZeroModeBoundaryCutoffWeight cutoff x *
      criticalFeaturePositiveShiftPoleGammaDensity eta x

theorem tendsto_criticalFeatureCompactFullBoundaryObservableAtPhase
    (theta : ℝ) (cutoff : ℕ) :
    Tendsto (criticalFeatureCompactFullBoundaryObservableAtPhase theta cutoff)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (criticalFeatureCompactFullSourceBoundaryLimitAtPhase cutoff theta)) := by
  have hr : 0 ≤ (cutoff : ℝ) + 3 := by positivity
  have hrR : (cutoff : ℝ) + 3 < (cutoff : ℝ) + 4 := by linarith
  obtain ⟨Gamma, hGamma, hlim⟩ :=
    XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral
      (c := 0) (r := (cutoff : ℝ) + 3) (R := (cutoff : ℝ) + 4)
      hr hrR
      (continuous_criticalFeatureFullBoundaryCutoffWeight theta cutoff)
      (fun x hx => by
        apply criticalFeatureFullBoundaryCutoffWeight_eq_zero_of_not_mem theta cutoff
        simpa only [zero_sub, zero_add] using hx)
  obtain ⟨Gamma', hGamma', _hzero, hfull⟩ :=
    exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums cutoff
  have hsame : Gamma = Gamma' := by
    ext gamma
    rw [hGamma, hGamma']
    constructor <;> intro h <;> simpa using h
  rw [hfull theta, ← hsame]
  change Tendsto
    (fun eta : ℝ =>
      ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
        criticalFeatureFullBoundaryCutoffWeight theta cutoff x * boundaryDensity XiC eta x)
    (nhdsWithin (0 : ℝ) (Ioi 0)) _
  simpa only [zero_sub, zero_add] using hlim

theorem tendsto_criticalFeatureCompactZeroModeBoundaryObservable
    (cutoff : ℕ) :
    Tendsto (criticalFeatureCompactZeroModeBoundaryObservable cutoff)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (criticalFeatureCompactZeroModeSourceBoundaryLimit cutoff)) := by
  have hr : 0 ≤ (cutoff : ℝ) + 3 := by positivity
  have hrR : (cutoff : ℝ) + 3 < (cutoff : ℝ) + 4 := by linarith
  obtain ⟨Gamma, hGamma, hlim⟩ :=
    XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral
      (c := 0) (r := (cutoff : ℝ) + 3) (R := (cutoff : ℝ) + 4)
      hr hrR
      (continuous_criticalFeatureZeroModeBoundaryCutoffWeight cutoff)
      (fun x hx => by
        apply criticalFeatureZeroModeBoundaryCutoffWeight_eq_zero_of_not_mem cutoff
        simpa only [zero_sub, zero_add] using hx)
  obtain ⟨Gamma', hGamma', hzero, _hfull⟩ :=
    exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums cutoff
  have hsame : Gamma = Gamma' := by
    ext gamma
    rw [hGamma, hGamma']
    constructor <;> intro h <;> simpa using h
  rw [hzero, ← hsame]
  change Tendsto
    (fun eta : ℝ =>
      ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
        criticalFeatureZeroModeBoundaryCutoffWeight cutoff x * boundaryDensity XiC eta x)
    (nhdsWithin (0 : ℝ) (Ioi 0)) _
  simpa only [zero_sub, zero_add] using hlim

theorem criticalFeatureCompactFullBoundaryObservableAtPhase_eq_poleGamma
    (theta : ℝ) (cutoff : ℕ) {eta : ℝ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2) :
    criticalFeatureCompactFullBoundaryObservableAtPhase theta cutoff eta =
      criticalFeatureCompactFullPoleGammaObservableAtPhase theta cutoff eta := by
  rw [criticalFeatureCompactFullBoundaryObservableAtPhase,
    criticalFeatureCompactFullPoleGammaObservableAtPhase]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards
    [ae_boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity heta0 hetaHalf]
    with x hx
  rw [hx]
  intro _hx
  rfl

theorem criticalFeatureCompactZeroModeBoundaryObservable_eq_poleGamma
    (cutoff : ℕ) {eta : ℝ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2) :
    criticalFeatureCompactZeroModeBoundaryObservable cutoff eta =
      criticalFeatureCompactZeroModePoleGammaObservable cutoff eta := by
  rw [criticalFeatureCompactZeroModeBoundaryObservable,
    criticalFeatureCompactZeroModePoleGammaObservable]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards
    [ae_boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity heta0 hetaHalf]
    with x hx
  rw [hx]
  intro _hx
  rfl

theorem tendsto_criticalFeatureCompactFullPoleGammaObservableAtPhase
    (theta : ℝ) (cutoff : ℕ) :
    Tendsto (criticalFeatureCompactFullPoleGammaObservableAtPhase theta cutoff)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (criticalFeatureCompactFullSourceBoundaryLimitAtPhase cutoff theta)) := by
  have hsource :=
    tendsto_criticalFeatureCompactFullBoundaryObservableAtPhase theta cutoff
  apply hsource.congr'
  have hhalf : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hhalf] with eta heta0 hetaHalf
  exact criticalFeatureCompactFullBoundaryObservableAtPhase_eq_poleGamma
    theta cutoff heta0 hetaHalf

theorem tendsto_criticalFeatureCompactZeroModePoleGammaObservable
    (cutoff : ℕ) :
    Tendsto (criticalFeatureCompactZeroModePoleGammaObservable cutoff)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (criticalFeatureCompactZeroModeSourceBoundaryLimit cutoff)) := by
  have hsource := tendsto_criticalFeatureCompactZeroModeBoundaryObservable cutoff
  apply hsource.congr'
  have hhalf : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hhalf] with eta heta0 hetaHalf
  exact criticalFeatureCompactZeroModeBoundaryObservable_eq_poleGamma
    cutoff heta0 hetaHalf

private theorem eventually_abs_sub_lt_of_tendsto_boundaryPhase
    {alpha : Type*} {l : Filter alpha} {f : alpha → ℝ} {a eps : ℝ}
    (h : Tendsto f l (nhds a)) (heps : 0 < eps) :
    ∀ᶠ x in l, |f x - a| < eps := by
  have hlo : ∀ᶠ x in l, a - eps < f x :=
    (tendsto_order.1 h).1 _ (by linarith)
  have hhi : ∀ᶠ x in l, f x < a + eps :=
    (tendsto_order.1 h).2 _ (by linarith)
  filter_upwards [hlo, hhi] with x hxlo hxhi
  rw [abs_lt]
  constructor <;> linarith

/-- Smooth source contribution omitted when the complete translated integer periodization is
restricted to the canonical finite lattice. -/
def criticalFeatureCompactTranslatedBaseOmittedCenters
    (n : ℕ) (eta theta : ℝ) : ℝ :=
  criticalFeatureCompactFullPoleGammaObservableAtPhase theta n eta -
    criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
      (criticalFeatureCanonicalLatticeWindow n) n eta

/-- Change in the literal finite-lattice observable between the boundary-selection cutoff and the
outer Plemelj cutoff. -/
def criticalFeatureCanonicalBoundarySelectedExteriorIncrement
    (n cutoff : ℕ) (eta theta : ℝ) : ℝ :=
  criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
      (criticalFeatureCanonicalLatticeWindow n) cutoff eta -
    criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
      (criticalFeatureCanonicalLatticeWindow n) n eta

/-- Exact smooth-cutoff decomposition.  Unlike the hard-core decomposition, every term here uses
the same cutoff that selected the boundary phase. -/
theorem criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance_eq_boundaryPieces
    (n cutoff : ℕ) (eta theta : ℝ) :
    criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
        n cutoff eta theta =
      (criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
          (criticalFeatureCanonicalLatticeWindow n) -
        criticalFeatureCompactZeroModePoleGammaObservable n eta) -
      (criticalFeatureCompactFullPoleGammaObservableAtPhase theta n eta -
        criticalFeatureCompactZeroModePoleGammaObservable n eta) +
      criticalFeatureCompactTranslatedBaseOmittedCenters n eta theta -
      criticalFeatureCanonicalBoundarySelectedExteriorIncrement n cutoff eta theta := by
  rw [criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance,
    criticalFeatureCompactTranslatedBaseOmittedCenters,
    criticalFeatureCanonicalBoundarySelectedExteriorIncrement]
  ring

/-- Boundary-first phase selection persists at every sufficiently small fixed positive shift,
with an explicit two-error loss and no moving-phase limit interchange. -/
theorem neg_criticalFeatureCompactFullPoleGammaObservableAtBoundaryPhase_sub_zeroMode_lt
    (n : ℕ) {eta eps : ℝ}
    (hfull :
      |criticalFeatureCompactFullPoleGammaObservableAtPhase
          (criticalFeatureCompactBoundaryDealiasingPhase n) n eta -
        criticalFeatureCompactFullSourceBoundaryLimitAtPhase n
          (criticalFeatureCompactBoundaryDealiasingPhase n)| < eps)
    (hzero :
      |criticalFeatureCompactZeroModePoleGammaObservable n eta -
        criticalFeatureCompactZeroModeSourceBoundaryLimit n| < eps) :
    -(criticalFeatureCompactFullPoleGammaObservableAtPhase
        (criticalFeatureCompactBoundaryDealiasingPhase n) n eta -
      criticalFeatureCompactZeroModePoleGammaObservable n eta) < 2 * eps := by
  have hphase := criticalFeatureCompactBoundaryDealiasingPhase_spec n
  rw [criticalFeatureCompactSourceBoundaryAliasAtPhase] at hphase
  rw [abs_lt] at hfull hzero
  linarith

/-- Source-only data chosen in the logically valid order: boundary phase, outer cutoff, then
positive displacement. -/
structure CriticalFeatureCanonicalBoundarySelectedData (n : ℕ) where
  cutoff : ℕ
  cutoff_ge : n ≤ cutoff
  displacement : ℝ
  displacement_pos : 0 < displacement
  displacement_lt_half : displacement < 1 / 2
  displacement_lt_reciprocal : displacement < 1 / ((n : ℝ) + 1)
  covariance_error_lt :
    |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n cutoff
          displacement (criticalFeatureCompactBoundaryDealiasingPhase n) -
        criticalFeatureTranslatedPoleGammaPlemeljCovariance
          (-(criticalFeatureCompactBoundaryDealiasingPhase n))
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1)
  full_boundary_error_lt :
    |criticalFeatureCompactFullPoleGammaObservableAtPhase
          (criticalFeatureCompactBoundaryDealiasingPhase n) n displacement -
        criticalFeatureCompactFullSourceBoundaryLimitAtPhase n
          (criticalFeatureCompactBoundaryDealiasingPhase n)| <
      1 / ((n : ℝ) + 1)
  zero_boundary_error_lt :
    |criticalFeatureCompactZeroModePoleGammaObservable n displacement -
        criticalFeatureCompactZeroModeSourceBoundaryLimit n| <
      1 / ((n : ℝ) + 1)

/-- Boundary-first finite source data exist unconditionally.  This is the quantifier reversal:
phase does not depend on either selected cutoff or displacement. -/
theorem exists_criticalFeatureCanonicalBoundarySelectedData (n : ℕ) :
    Nonempty (CriticalFeatureCanonicalBoundarySelectedData n) := by
  let K := criticalFeatureCanonicalLatticeWindow n
  let theta := criticalFeatureCompactBoundaryDealiasingPhase n
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have heps : 0 < eps := by positivity
  have houter : Tendsto
      (criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K)
      atTop
      (nhds (criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K)) := by
    have h :=
      tendsto_criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K
    convert h using 1
    rw [criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget_eq_sourceCovariance_add_vm]
    ring_nf
  have houterNear : ∀ᶠ cutoff : ℕ in atTop,
      |criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K cutoff -
        criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K| < eps / 2 :=
    eventually_abs_sub_lt_of_tendsto_boundaryPhase houter (half_pos heps)
  obtain ⟨cutoff, hcutoffNear, hcutoffGe⟩ :=
    (houterNear.and (eventually_ge_atTop n)).exists
  have hinner :=
    tendsto_criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
      n cutoff theta
  have hinnerNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
          n cutoff eta theta -
        criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K cutoff| <
        eps / 2 :=
    eventually_abs_sub_lt_of_tendsto_boundaryPhase hinner (half_pos heps)
  have hfullNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      |criticalFeatureCompactFullPoleGammaObservableAtPhase theta n eta -
        criticalFeatureCompactFullSourceBoundaryLimitAtPhase n theta| < eps :=
    eventually_abs_sub_lt_of_tendsto_boundaryPhase
      (tendsto_criticalFeatureCompactFullPoleGammaObservableAtPhase theta n) heps
  have hzeroNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      |criticalFeatureCompactZeroModePoleGammaObservable n eta -
        criticalFeatureCompactZeroModeSourceBoundaryLimit n| < eps :=
    eventually_abs_sub_lt_of_tendsto_boundaryPhase
      (tendsto_criticalFeatureCompactZeroModePoleGammaObservable n) heps
  have hpos : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < eta :=
    self_mem_nhdsWithin
  have hhalf : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  have hepsNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), eta < eps :=
    (eventually_lt_nhds heps).filter_mono inf_le_left
  obtain ⟨eta, hetaPos, hetaHalf, hetaEps, hetaInner, hetaFull, hetaZero⟩ :=
    (hpos.and (hhalf.and (hepsNear.and
      (hinnerNear.and (hfullNear.and hzeroNear))))).exists
  refine ⟨{
    cutoff := cutoff
    cutoff_ge := hcutoffGe
    displacement := eta
    displacement_pos := hetaPos
    displacement_lt_half := hetaHalf
    displacement_lt_reciprocal := ?_
    covariance_error_lt := ?_
    full_boundary_error_lt := ?_
    zero_boundary_error_lt := ?_ }⟩
  · simpa only [eps] using hetaEps
  · have htriangle :
        |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
              n cutoff eta theta -
            criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K| ≤
          |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
              n cutoff eta theta -
            criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K cutoff| +
          |criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K cutoff -
            criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K| := by
        rw [show
          criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
                n cutoff eta theta -
              criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K =
            (criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
                n cutoff eta theta -
              criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff
                (-theta) K cutoff) +
            (criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff
                (-theta) K cutoff -
              criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K) by ring]
        exact abs_add_le _ _
    change
      |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
            n cutoff eta theta -
          criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K| < eps
    exact htriangle.trans_lt (by linarith)
  · simpa only [theta, eps] using hetaFull
  · simpa only [eps] using hetaZero

/-- Canonical boundary-first cutoff and positive displacement. -/
def criticalFeatureCanonicalBoundarySelectedData (n : ℕ) :
    CriticalFeatureCanonicalBoundarySelectedData n :=
  Classical.choice (exists_criticalFeatureCanonicalBoundarySelectedData n)

/-- Finite source majorant after boundary-first phase selection.  No zero or divisor index occurs
in the definition. -/
def criticalFeatureCanonicalBoundarySelectedSourceMajorant (n : ℕ) : ℝ :=
  let data := criticalFeatureCanonicalBoundarySelectedData n
  let theta := criticalFeatureCompactBoundaryDealiasingPhase n
  (criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
      (criticalFeatureCanonicalLatticeWindow n) -
    criticalFeatureCompactZeroModePoleGammaObservable n data.displacement) +
  |criticalFeatureCompactTranslatedBaseOmittedCenters n data.displacement theta| +
  |criticalFeatureCanonicalBoundarySelectedExteriorIncrement
    n data.cutoff data.displacement theta| +
  2 * (1 / ((n : ℝ) + 1))

/-- Selected finite covariance is bounded by the boundary-first source majorant. -/
theorem criticalFeatureCanonicalBoundarySelectedFiniteCovariance_le_majorant (n : ℕ) :
    criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n
        (criticalFeatureCanonicalBoundarySelectedData n).cutoff
        (criticalFeatureCanonicalBoundarySelectedData n).displacement
        (criticalFeatureCompactBoundaryDealiasingPhase n) ≤
      criticalFeatureCanonicalBoundarySelectedSourceMajorant n := by
  let data := criticalFeatureCanonicalBoundarySelectedData n
  let theta := criticalFeatureCompactBoundaryDealiasingPhase n
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have halias :=
    neg_criticalFeatureCompactFullPoleGammaObservableAtBoundaryPhase_sub_zeroMode_lt
      n data.full_boundary_error_lt data.zero_boundary_error_lt
  have homit := le_abs_self
    (criticalFeatureCompactTranslatedBaseOmittedCenters n data.displacement theta)
  have hext := neg_le_abs
    (criticalFeatureCanonicalBoundarySelectedExteriorIncrement
      n data.cutoff data.displacement theta)
  dsimp only [data, theta, eps] at halias homit hext
  rw [criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance_eq_boundaryPieces]
  simp only [criticalFeatureCanonicalBoundarySelectedSourceMajorant]
  linarith

end

end RHTower

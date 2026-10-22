import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureTranslatedPhaseFiniteSourceDecomposition

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

/-! ## Finite-lattice phase-average selection

The preceding full-periodization selector still records omitted centers explicitly.  A sharper
choice averages the actual finite lattice at the boundary and selects a phase above that exact
average.  This removes both the Fourier alias and the omitted-center term. -/

theorem criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_finite_mul_cutoff
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) (x : ℝ) :
    criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta K cutoff x =
      criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K x *
        SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) x := by
  rw [criticalFeatureTranslatedLatticeBoundaryCutoffWeight,
    criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight]
  simp only [criticalFeatureBoundaryCutoffWeight]
  exact (Finset.sum_mul K
    (fun k : ℤ => criticalFeatureRealBoundaryWeight ((k : ℝ) - theta) x)
    (SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) x)).symm

theorem continuous_criticalFeatureTranslatedLatticeBoundaryCutoffWeight_phase
    (K : Finset ℤ) (cutoff : ℕ) (x : ℝ) :
    Continuous (fun theta : ℝ =>
      criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta K cutoff x) := by
  simp_rw [criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_finite_mul_cutoff]
  exact (continuous_criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_phase K x).mul
    continuous_const

/-- Boundary value of the actual finite translated lattice.  Definition is a compact source
limit and contains no zero or divisor index. -/
def criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase
    (n : ℕ) (theta : ℝ) : ℝ :=
  limUnder (nhdsWithin (0 : ℝ) (Ioi 0))
    (criticalFeatureTranslatedCompactLatticeBoundaryObservable theta
      (criticalFeatureCanonicalLatticeWindow n) n)

/-- One common finite real-zero packet represents the whole finite-lattice boundary phase family.
The packet is used only to prove continuity, never in source definitions. -/
theorem exists_criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseFamily_eq_realZeroSums
    (n : ℕ) :
    ∃ Gamma : Finset ℝ,
      (∀ gamma : ℝ, gamma ∈ Gamma ↔
        ((gamma : ℂ) ∈ Metric.ball (0 : ℂ) ((n : ℝ) + 4) ∧
          XiC (gamma : ℂ) = 0)) ∧
      ∀ theta : ℝ,
        criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n theta =
          ∑ gamma ∈ Gamma,
            ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
              criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta
                (criticalFeatureCanonicalLatticeWindow n) n gamma := by
  obtain ⟨Gamma, hGamma, _hzero, _hfull⟩ :=
    exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums n
  refine ⟨Gamma, hGamma, ?_⟩
  intro theta
  have hr : 0 ≤ (n : ℝ) + 3 := by positivity
  have hrR : (n : ℝ) + 3 < (n : ℝ) + 4 := by linarith
  obtain ⟨GammaTheta, hGammaTheta, hlim⟩ :=
    XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral
      (c := 0) (r := (n : ℝ) + 3) (R := (n : ℝ) + 4)
      hr hrR
      (continuous_criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta
        (criticalFeatureCanonicalLatticeWindow n) n)
      (fun x hx => by
        apply criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_zero_of_not_mem
          theta (criticalFeatureCanonicalLatticeWindow n) n
        simpa only [zero_sub, zero_add] using hx)
  have hsame : GammaTheta = Gamma := by
    ext gamma
    rw [hGammaTheta, hGamma]
    constructor <;> intro h <;> simpa using h
  rw [criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase]
  change limUnder (nhdsWithin (0 : ℝ) (Ioi 0))
      (fun eta : ℝ =>
        ∫ x in Icc (-((n : ℝ) + 3)) ((n : ℝ) + 3),
          criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta
              (criticalFeatureCanonicalLatticeWindow n) n x *
            boundaryDensity XiC eta x) = _
  rw [← hsame]
  simpa only [zero_sub, zero_add] using hlim.limUnder_eq

theorem continuous_criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase
    (n : ℕ) :
    Continuous (criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n) := by
  obtain ⟨Gamma, _hGamma, hformula⟩ :=
    exists_criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseFamily_eq_realZeroSums n
  have heq : criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n =
      fun theta : ℝ =>
        ∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta
              (criticalFeatureCanonicalLatticeWindow n) n gamma := by
    funext theta
    exact hformula theta
  rw [heq]
  exact continuous_finsetSum Gamma fun gamma _hgamma =>
    continuous_const.mul
      (continuous_criticalFeatureTranslatedLatticeBoundaryCutoffWeight_phase
        (criticalFeatureCanonicalLatticeWindow n) n gamma)

/-- Exact source boundary phase average of the actual finite lattice. -/
def criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage (n : ℕ) : ℝ :=
  ∫ theta in (0 : ℝ)..1,
    criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n theta

private theorem exists_intervalIntegral_le_value_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ x ∈ Icc (0 : ℝ) 1, (∫ theta in (0 : ℝ)..1, f theta) ≤ f x := by
  have hnonempty : (Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr (by norm_num)
  obtain ⟨x, hxmem, hxmax⟩ :=
    isCompact_Icc.exists_isMaxOn hnonempty hf.continuousOn
  refine ⟨x, hxmem, ?_⟩
  have hmono :
      (∫ theta in (0 : ℝ)..1, f theta) ≤ ∫ _theta in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_mono_on (by norm_num)
      (hf.intervalIntegrable _ _) intervalIntegrable_const
      (fun theta htheta => hxmax htheta)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono

theorem exists_criticalFeatureCompactFiniteLatticeBoundaryAveragePhase (n : ℕ) :
    ∃ theta ∈ Icc (0 : ℝ) 1,
      criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n ≤
        criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n theta := by
  simpa only [criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage] using
    exists_intervalIntegral_le_value_of_continuous
      (continuous_criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n)

/-- Canonical source phase selected above the exact finite-lattice boundary average. -/
def criticalFeatureCompactFiniteLatticeBoundaryAveragePhase (n : ℕ) : ℝ :=
  Classical.choose (exists_criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n)

theorem criticalFeatureCompactFiniteLatticeBoundaryAveragePhase_mem (n : ℕ) :
    criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n ∈ Icc (0 : ℝ) 1 :=
  (Classical.choose_spec
    (exists_criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n)).1

theorem criticalFeatureCompactFiniteLatticeBoundaryAveragePhase_spec (n : ℕ) :
    criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n ≤
      criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n
        (criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n) :=
  (Classical.choose_spec
    (exists_criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n)).2

/-- At every fixed phase, the finite-lattice pole--Gamma evaluation converges to its source-defined
boundary value. -/
theorem tendsto_criticalFeatureCompactFiniteLatticePoleGammaObservableAtPhase
    (n : ℕ) (theta : ℝ) :
    Tendsto
      (criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
        (criticalFeatureCanonicalLatticeWindow n) n)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n theta)) := by
  have hboundary :=
    tendsto_criticalFeatureTranslatedCompactLatticeBoundaryObservable theta
      (criticalFeatureCanonicalLatticeWindow n) n
  have hpoleGamma :=
    tendsto_criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
      (criticalFeatureCanonicalLatticeWindow n) n
  rw [criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase,
    hboundary.limUnder_eq]
  exact hpoleGamma

/-- Source-only finite-lattice average data, selected in the order phase, outer cutoff,
displacement. -/
structure CriticalFeatureCanonicalFiniteLatticeAverageSelectedData (n : ℕ) where
  cutoff : ℕ
  cutoff_ge : n ≤ cutoff
  displacement : ℝ
  displacement_pos : 0 < displacement
  displacement_lt_half : displacement < 1 / 2
  displacement_lt_reciprocal : displacement < 1 / ((n : ℝ) + 1)
  covariance_error_lt :
    |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n cutoff
          displacement (criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n) -
        criticalFeatureTranslatedPoleGammaPlemeljCovariance
          (-(criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n))
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1)
  boundary_error_lt :
    |criticalFeatureTranslatedCompactLatticePoleGammaObservable
          (criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n)
          (criticalFeatureCanonicalLatticeWindow n) n displacement -
        criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n
          (criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n)| <
      1 / ((n : ℝ) + 1)

theorem exists_criticalFeatureCanonicalFiniteLatticeAverageSelectedData (n : ℕ) :
    Nonempty (CriticalFeatureCanonicalFiniteLatticeAverageSelectedData n) := by
  let K := criticalFeatureCanonicalLatticeWindow n
  let theta := criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n
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
  have hboundaryNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      |criticalFeatureTranslatedCompactLatticePoleGammaObservable theta K n eta -
        criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n theta| < eps :=
    eventually_abs_sub_lt_of_tendsto_boundaryPhase
      (tendsto_criticalFeatureCompactFiniteLatticePoleGammaObservableAtPhase n theta) heps
  have hpos : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < eta :=
    self_mem_nhdsWithin
  have hhalf : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  have hepsNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), eta < eps :=
    (eventually_lt_nhds heps).filter_mono inf_le_left
  obtain ⟨eta, hetaPos, hetaHalf, hetaEps, hetaInner, hetaBoundary⟩ :=
    (hpos.and (hhalf.and (hepsNear.and (hinnerNear.and hboundaryNear)))).exists
  refine ⟨{
    cutoff := cutoff
    cutoff_ge := hcutoffGe
    displacement := eta
    displacement_pos := hetaPos
    displacement_lt_half := hetaHalf
    displacement_lt_reciprocal := ?_
    covariance_error_lt := ?_
    boundary_error_lt := ?_ }⟩
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
  · simpa only [theta, K, eps] using hetaBoundary

/-- Canonical finite-lattice-average source selection. -/
def criticalFeatureCanonicalFiniteLatticeAverageSelectedData (n : ℕ) :
    CriticalFeatureCanonicalFiniteLatticeAverageSelectedData n :=
  Classical.choice (exists_criticalFeatureCanonicalFiniteLatticeAverageSelectedData n)

/-- Sharper source majorant: actual finite phase average replaces full zero mode plus omitted
centers. -/
def criticalFeatureCanonicalFiniteLatticeAverageSourceMajorant (n : ℕ) : ℝ :=
  let data := criticalFeatureCanonicalFiniteLatticeAverageSelectedData n
  let theta := criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n
  criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
      (criticalFeatureCanonicalLatticeWindow n) -
    criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n +
    |criticalFeatureCanonicalBoundarySelectedExteriorIncrement
      n data.cutoff data.displacement theta| +
    1 / ((n : ℝ) + 1)

/-- Exact finite-lattice phase averaging removes both nonzero Fourier alias and omitted-center
loss.  Only the literal exterior cutoff increment and vanishing selection error remain. -/
theorem criticalFeatureCanonicalFiniteLatticeAverageSelectedCovariance_le_majorant (n : ℕ) :
    criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n
        (criticalFeatureCanonicalFiniteLatticeAverageSelectedData n).cutoff
        (criticalFeatureCanonicalFiniteLatticeAverageSelectedData n).displacement
        (criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n) ≤
      criticalFeatureCanonicalFiniteLatticeAverageSourceMajorant n := by
  let data := criticalFeatureCanonicalFiniteLatticeAverageSelectedData n
  let theta := criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have hphase := criticalFeatureCompactFiniteLatticeBoundaryAveragePhase_spec n
  have hboundary := data.boundary_error_lt
  rw [abs_lt] at hboundary
  have hext := neg_le_abs
    (criticalFeatureCanonicalBoundarySelectedExteriorIncrement
      n data.cutoff data.displacement theta)
  have hdecomp :
      criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
          n data.cutoff data.displacement theta =
        criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
            (criticalFeatureCanonicalLatticeWindow n) -
          criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
            (criticalFeatureCanonicalLatticeWindow n) n data.displacement -
          criticalFeatureCanonicalBoundarySelectedExteriorIncrement
            n data.cutoff data.displacement theta := by
    rw [criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance,
      criticalFeatureCanonicalBoundarySelectedExteriorIncrement]
    ring
  dsimp only [data, theta, eps] at hphase hboundary hext hdecomp
  rw [hdecomp]
  simp only [criticalFeatureCanonicalFiniteLatticeAverageSourceMajorant]
  linarith

/-- Selected finite covariance differs from infinite translated source covariance by the explicit
submicroscopic error. -/
theorem abs_criticalFeatureCanonicalFiniteLatticeAverageSelectedCovariance_sub_plemelj_lt
    (n : ℕ) :
    |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n
          (criticalFeatureCanonicalFiniteLatticeAverageSelectedData n).cutoff
          (criticalFeatureCanonicalFiniteLatticeAverageSelectedData n).displacement
          (criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n) -
        criticalFeatureTranslatedPoleGammaPlemeljCovariance
          (-(criticalFeatureCompactFiniteLatticeBoundaryAveragePhase n))
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1) :=
  (criticalFeatureCanonicalFiniteLatticeAverageSelectedData n).covariance_error_lt

/-! ## Whole-covariance height-cell phase selection -/

/-- Pole--Gamma safe-line jet is continuous in vertical height. -/
theorem continuous_criticalFeaturePoleGammaArchJet :
    Continuous (fun t : ℝ =>
      2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
        deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re) := by
  rw [continuous_iff_continuousAt]
  intro t
  let s := criticalFeatureEulerVMArchPoint t
  have hsre : s.re = 3 / 2 := by
    simpa [s] using criticalFeatureEulerVMArchPoint_re t
  have hspos : 0 < s.re := by
    rw [hsre]
    norm_num
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [zero_re] at hre
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re] at hre
    rw [hsre] at hre
    norm_num at hre
  have harch : AnalyticAt ℂ archFactor s := analyticAt_archFactor_of_re_pos hspos
  have harchNe : archFactor s ≠ 0 :=
    archFactor_ne_zero hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hspos)
  have hlog : AnalyticAt ℂ (logDeriv archFactor) s := by
    simpa only [logDeriv] using harch.deriv.div harch harchNe
  have hpoint : ContinuousAt criticalFeatureEulerVMArchPoint t := by
    unfold criticalFeatureEulerVMArchPoint
    fun_prop
  have hlogComp : ContinuousAt
      (fun u : ℝ => logDeriv archFactor (criticalFeatureEulerVMArchPoint u)) t :=
    hlog.continuousAt.comp_of_eq hpoint rfl
  have hderivComp : ContinuousAt
      (fun u : ℝ => deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint u)) t :=
    hlog.deriv.continuousAt.comp_of_eq hpoint rfl
  exact continuousAt_const.mul
    (Complex.continuous_re.continuousAt.comp (hlogComp.sub hderivComp))

theorem continuous_criticalFeatureTranslatedPoleGammaLatticeBudget_phase
    (K : Finset ℤ) :
    Continuous (fun theta : ℝ =>
      criticalFeatureTranslatedPoleGammaLatticeBudget (-theta) K) := by
  have hbase : Continuous (fun theta : ℝ =>
      criticalFeatureTranslatedPoleGammaLatticeBudget theta K) := by
    unfold criticalFeatureTranslatedPoleGammaLatticeBudget
    apply continuous_finsetSum K
    intro k hk
    exact continuous_criticalFeaturePoleGammaArchJet.comp
      (continuous_const.add continuous_id)
  exact hbase.comp continuous_neg

/-- Complete base-cutoff source covariance as a function of height-cell phase. -/
def criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase
    (n : ℕ) (theta : ℝ) : ℝ :=
  criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
      (criticalFeatureCanonicalLatticeWindow n) -
    criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n theta

theorem continuous_criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase
    (n : ℕ) :
    Continuous (criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase n) := by
  exact (continuous_criticalFeatureTranslatedPoleGammaLatticeBudget_phase
    (criticalFeatureCanonicalLatticeWindow n)).sub
      (continuous_criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n)

/-- Exact height-cell average of the complete finite-lattice source covariance. -/
def criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage (n : ℕ) : ℝ :=
  ∫ theta in (0 : ℝ)..1,
    criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase n theta

private theorem exists_value_le_intervalIntegral_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ x ∈ Icc (0 : ℝ) 1, f x ≤ ∫ theta in (0 : ℝ)..1, f theta := by
  have hnonempty : (Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr (by norm_num)
  obtain ⟨x, hxmem, hxmin⟩ :=
    isCompact_Icc.exists_isMinOn hnonempty hf.continuousOn
  refine ⟨x, hxmem, ?_⟩
  have hmono :
      (∫ _theta in (0 : ℝ)..1, f x) ≤ ∫ theta in (0 : ℝ)..1, f theta :=
    intervalIntegral.integral_mono_on (by norm_num)
      intervalIntegrable_const (hf.intervalIntegrable _ _)
      (fun theta htheta => hxmin htheta)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono

theorem exists_criticalFeatureCompactFiniteLatticeSourceCovariancePhase (n : ℕ) :
    ∃ theta ∈ Icc (0 : ℝ) 1,
      criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase n theta ≤
        criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n := by
  simpa only [criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage] using
    exists_value_le_intervalIntegral_of_continuous
      (continuous_criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase n)

/-- Canonical phase minimizing the complete source covariance below its exact height-cell
average. -/
def criticalFeatureCompactFiniteLatticeSourceCovariancePhase (n : ℕ) : ℝ :=
  Classical.choose (exists_criticalFeatureCompactFiniteLatticeSourceCovariancePhase n)

theorem criticalFeatureCompactFiniteLatticeSourceCovariancePhase_mem (n : ℕ) :
    criticalFeatureCompactFiniteLatticeSourceCovariancePhase n ∈ Icc (0 : ℝ) 1 :=
  (Classical.choose_spec
    (exists_criticalFeatureCompactFiniteLatticeSourceCovariancePhase n)).1

theorem criticalFeatureCompactFiniteLatticeSourceCovariancePhase_spec (n : ℕ) :
    criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase n
        (criticalFeatureCompactFiniteLatticeSourceCovariancePhase n) ≤
      criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n :=
  (Classical.choose_spec
    (exists_criticalFeatureCompactFiniteLatticeSourceCovariancePhase n)).2

/-- Finite realization data for the phase minimizing the complete source covariance. -/
structure CriticalFeatureCanonicalSourceCovariancePhaseData (n : ℕ) where
  cutoff : ℕ
  cutoff_ge : n ≤ cutoff
  displacement : ℝ
  displacement_pos : 0 < displacement
  displacement_lt_half : displacement < 1 / 2
  displacement_lt_reciprocal : displacement < 1 / ((n : ℝ) + 1)
  covariance_error_lt :
    |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n cutoff
          displacement (criticalFeatureCompactFiniteLatticeSourceCovariancePhase n) -
        criticalFeatureTranslatedPoleGammaPlemeljCovariance
          (-(criticalFeatureCompactFiniteLatticeSourceCovariancePhase n))
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1)
  boundary_error_lt :
    |criticalFeatureTranslatedCompactLatticePoleGammaObservable
          (criticalFeatureCompactFiniteLatticeSourceCovariancePhase n)
          (criticalFeatureCanonicalLatticeWindow n) n displacement -
        criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n
          (criticalFeatureCompactFiniteLatticeSourceCovariancePhase n)| <
      1 / ((n : ℝ) + 1)

theorem exists_criticalFeatureCanonicalSourceCovariancePhaseData (n : ℕ) :
    Nonempty (CriticalFeatureCanonicalSourceCovariancePhaseData n) := by
  let K := criticalFeatureCanonicalLatticeWindow n
  let theta := criticalFeatureCompactFiniteLatticeSourceCovariancePhase n
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
  have hboundaryNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      |criticalFeatureTranslatedCompactLatticePoleGammaObservable theta K n eta -
        criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n theta| < eps :=
    eventually_abs_sub_lt_of_tendsto_boundaryPhase
      (tendsto_criticalFeatureCompactFiniteLatticePoleGammaObservableAtPhase n theta) heps
  have hpos : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < eta :=
    self_mem_nhdsWithin
  have hhalf : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  have hepsNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), eta < eps :=
    (eventually_lt_nhds heps).filter_mono inf_le_left
  obtain ⟨eta, hetaPos, hetaHalf, hetaEps, hetaInner, hetaBoundary⟩ :=
    (hpos.and (hhalf.and (hepsNear.and (hinnerNear.and hboundaryNear)))).exists
  refine ⟨{
    cutoff := cutoff
    cutoff_ge := hcutoffGe
    displacement := eta
    displacement_pos := hetaPos
    displacement_lt_half := hetaHalf
    displacement_lt_reciprocal := ?_
    covariance_error_lt := ?_
    boundary_error_lt := ?_ }⟩
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
  · simpa only [theta, K, eps] using hetaBoundary

/-- Canonical finite realization at the covariance-minimizing height-cell phase. -/
def criticalFeatureCanonicalSourceCovariancePhaseData (n : ℕ) :
    CriticalFeatureCanonicalSourceCovariancePhaseData n :=
  Classical.choice (exists_criticalFeatureCanonicalSourceCovariancePhaseData n)

/-- Height-cell source majorant.  Its only finite-realization loss is the exterior cutoff
increment; the leading statistic is an exact phase average independent of selected phase. -/
def criticalFeatureCanonicalHeightCellSourceMajorant (n : ℕ) : ℝ :=
  let data := criticalFeatureCanonicalSourceCovariancePhaseData n
  let theta := criticalFeatureCompactFiniteLatticeSourceCovariancePhase n
  criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n +
    |criticalFeatureCanonicalBoundarySelectedExteriorIncrement
      n data.cutoff data.displacement theta| +
    1 / ((n : ℝ) + 1)

theorem criticalFeatureCanonicalSourceCovariancePhaseFiniteCovariance_le_majorant (n : ℕ) :
    criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n
        (criticalFeatureCanonicalSourceCovariancePhaseData n).cutoff
        (criticalFeatureCanonicalSourceCovariancePhaseData n).displacement
        (criticalFeatureCompactFiniteLatticeSourceCovariancePhase n) ≤
      criticalFeatureCanonicalHeightCellSourceMajorant n := by
  let data := criticalFeatureCanonicalSourceCovariancePhaseData n
  let theta := criticalFeatureCompactFiniteLatticeSourceCovariancePhase n
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have hphase := criticalFeatureCompactFiniteLatticeSourceCovariancePhase_spec n
  have hboundary := data.boundary_error_lt
  rw [abs_lt] at hboundary
  have hext := neg_le_abs
    (criticalFeatureCanonicalBoundarySelectedExteriorIncrement
      n data.cutoff data.displacement theta)
  have hdecomp :
      criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
          n data.cutoff data.displacement theta =
        criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
            (criticalFeatureCanonicalLatticeWindow n) -
          criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
            (criticalFeatureCanonicalLatticeWindow n) n data.displacement -
          criticalFeatureCanonicalBoundarySelectedExteriorIncrement
            n data.cutoff data.displacement theta := by
    rw [criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance,
      criticalFeatureCanonicalBoundarySelectedExteriorIncrement]
    ring
  rw [criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase] at hphase
  dsimp only [data, theta, eps] at hphase hboundary hext hdecomp
  rw [hdecomp]
  simp only [criticalFeatureCanonicalHeightCellSourceMajorant]
  linarith

theorem abs_criticalFeatureCanonicalSourceCovariancePhaseFiniteCovariance_sub_plemelj_lt
    (n : ℕ) :
    |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n
          (criticalFeatureCanonicalSourceCovariancePhaseData n).cutoff
          (criticalFeatureCanonicalSourceCovariancePhaseData n).displacement
          (criticalFeatureCompactFiniteLatticeSourceCovariancePhase n) -
        criticalFeatureTranslatedPoleGammaPlemeljCovariance
          (-(criticalFeatureCompactFiniteLatticeSourceCovariancePhase n))
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1) :=
  (criticalFeatureCanonicalSourceCovariancePhaseData n).covariance_error_lt

theorem criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage_eq_channels
    (n : ℕ) :
    criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n =
      (∫ theta in (0 : ℝ)..1,
        criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
          (criticalFeatureCanonicalLatticeWindow n)) -
      criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n := by
  rw [criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage,
    criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage]
  simp_rw [criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase]
  rw [intervalIntegral.integral_sub]
  · exact (continuous_criticalFeatureTranslatedPoleGammaLatticeBudget_phase
      (criticalFeatureCanonicalLatticeWindow n)).intervalIntegrable _ _
  · exact (continuous_criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n).intervalIntegrable _ _

/-- Averaging a translated pole--Gamma lattice through one height phase tiles its centers into
the corresponding ordinary vertical unit cells.  This is an exact source identity: no divisor,
zero packet, or Fourier alias occurs. -/
theorem phaseAverage_criticalFeatureTranslatedPoleGammaLatticeBudget_eq_heightCells
    (K : Finset ℤ) :
    (∫ theta : ℝ in (0 : ℝ)..1,
      criticalFeatureTranslatedPoleGammaLatticeBudget (-theta) K) =
      ∑ k ∈ K, ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ),
        2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
          deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re := by
  unfold criticalFeatureTranslatedPoleGammaLatticeBudget
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    simpa only [sub_eq_add_neg, neg_zero, add_zero] using
      (intervalIntegral.integral_comp_sub_left
        (fun t : ℝ =>
          2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
            deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re)
        (k : ℝ) (a := (0 : ℝ)) (b := 1))
  · intro k hk
    have hc : Continuous fun theta : ℝ =>
        2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint ((k : ℝ) + -theta)) -
          deriv (logDeriv archFactor)
            (criticalFeatureEulerVMArchPoint ((k : ℝ) + -theta))).re :=
      continuous_criticalFeaturePoleGammaArchJet.comp (continuous_const.add continuous_id.neg)
    exact hc.intervalIntegrable 0 1

/-- The complete phase-selected source statistic has no residual lattice alias: it is exactly a
finite vertical pole--Gamma cell integral minus the compact source boundary average. -/
theorem criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage_eq_heightCells
    (n : ℕ) :
    criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n =
      (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
        ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ),
          2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
            deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re) -
      criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n := by
  rw [criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage_eq_channels,
    phaseAverage_criticalFeatureTranslatedPoleGammaLatticeBudget_eq_heightCells]

end

end RHTower

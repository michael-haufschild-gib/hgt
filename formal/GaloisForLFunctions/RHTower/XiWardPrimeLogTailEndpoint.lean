import GaloisForLFunctions.RHTower.XiWardPrimeLogSampledGramLaw
import GaloisForLFunctions.RHTower.XiWardMergedSlackPrimeLogSampling
import GaloisForLFunctions.RHTower.XiWardEdgeSymmetryHalfCriterion
import GaloisForLFunctions.RHTower.XiWardInteriorSourceBudgetDivergence

/-!
# Prime-log tail endpoints for the Xi Ward law

The generic sampled Ward criteria require a proof that the chosen sample set
meets every detection window.  For the canonical prime-log sample family, Lean
already supplies that cover beyond a cutoff.  This module absorbs that side
condition into closed tail criteria and identifies the weakest current scalar
burden after exact detector-variation and real-channel reduction.
-/

namespace RHTower

/-- Adaptive real allowance is even in sample height. -/
theorem xiWardAdaptiveRealSampleSlack_abs (t : ℝ) :
    xiWardAdaptiveRealSampleSlack |t| = xiWardAdaptiveRealSampleSlack t := by
  simp [xiWardAdaptiveRealSampleSlack, xiWardRefinedMarginProxy]

/-- Real Ward channel at Euler edge depends only on absolute height. -/
theorem re_continuedXiAntiCausalWardResponse_eulerEdge_abs (t : ℝ) :
    (continuedXiAntiCausalWardResponse
      ((1 / 2 : ℂ) + Complex.I * ((|t| : ℝ) : ℂ))).re =
    (continuedXiAntiCausalWardResponse
      ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).re := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    exact re_continuedXiAntiCausalWardResponse_eulerEdge_even t

/-- Height symmetry removes the duplicate negative half of every real-channel
sample family. -/
theorem continuedXiWardRefinedSlackSampledRealLaw_abs_image_iff (S : Set ℝ) :
    ContinuedXiWardRefinedSlackSampledRealLaw (abs '' S) ↔
      ContinuedXiWardRefinedSlackSampledRealLaw S := by
  constructor
  · intro h t ht
    calc
      (continuedXiAntiCausalWardResponse
          ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).re =
          (continuedXiAntiCausalWardResponse
            ((1 / 2 : ℂ) + Complex.I * ((|t| : ℝ) : ℂ))).re :=
        (re_continuedXiAntiCausalWardResponse_eulerEdge_abs t).symm
      _ ≤ 2 + xiWardAdaptiveRealSampleSlack |t| :=
        h |t| ⟨t, ht, rfl⟩
      _ = 2 + xiWardAdaptiveRealSampleSlack t := by
        rw [xiWardAdaptiveRealSampleSlack_abs]
  · intro h t ht
    obtain ⟨u, hu, rfl⟩ := ht
    calc
      (continuedXiAntiCausalWardResponse
          ((1 / 2 : ℂ) + Complex.I * ((|u| : ℝ) : ℂ))).re =
          (continuedXiAntiCausalWardResponse
            ((1 / 2 : ℂ) + Complex.I * (u : ℂ))).re :=
        re_continuedXiAntiCausalWardResponse_eulerEdge_abs u
      _ ≤ 2 + xiWardAdaptiveRealSampleSlack u := h u hu
      _ = 2 + xiWardAdaptiveRealSampleSlack |u| := by
        rw [xiWardAdaptiveRealSampleSlack_abs]

theorem xiWardAdaptiveRealSampleSlack_lt_one (t : ℝ) :
    xiWardAdaptiveRealSampleSlack t < 1 := by
  have hmono := xiWardDetectorRealExcess_mono
    (xiWardRefinedMarginProxy_pos t).le
    (xiWardRefinedMarginProxy_le_inv1024 t) (le_refl (1 / 1024 : ℝ))
  have htop : xiWardDetectorRealExcess (1 / 1024) < 1 := by
    norm_num [xiWardDetectorRealExcess]
  exact lt_of_le_of_lt hmono htop

/-- Fixed-line Harnack followed by the reflected source-only majorant cannot
close the adaptive endpoint even cofinally: that majorant diverges at every
height, while the adaptive allowance remains below one. -/
theorem not_cofinally_xiWardFixedInteriorMajorant_closes_adaptiveRealLaw :
    ¬ ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧
      4 * xiWardInteriorSourceArithmeticBound
          ((2 : ℂ) + Complex.I * (t : ℂ)) ≤
        2 + xiWardAdaptiveRealSampleSlack t := by
  intro h
  have hdiv := xiWardInteriorSourceArithmeticBound_vertical_tendsto_atTop
    (h := 2) (by norm_num)
  have heventually : ∀ᶠ t : ℝ in Filter.atTop,
      1 ≤ xiWardInteriorSourceArithmeticBound
        ((2 : ℂ) + Complex.I * (t : ℂ)) :=
    (Filter.tendsto_atTop.1 hdiv) 1
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 heventually
  obtain ⟨t, ht, hclose⟩ := h T
  have hlower := hT t ht
  have hslack := xiWardAdaptiveRealSampleSlack_lt_one t
  linarith

/-- The canonical prime-log Ward scalar estimate need only hold eventually;
the arithmetic detection-cover side condition is discharged inside endpoint. -/
def ContinuedXiWardPrimeLogTailScalarLaw : Prop :=
  ∃ y₀ : ℝ, ∀ Y : ℝ, y₀ ≤ Y →
    ContinuedXiWardSampledScalarLaw (xiWardPrimeLogSampleSet Y)

/-- The same prime-log tail criterion with the four-unit budget relaxed by the
local zero-free margin.  This is the weaker scalar endpoint. -/
def ContinuedXiWardPrimeLogTailMergedSlackLaw : Prop :=
  ∃ y₀ : ℝ, ∀ Y : ℝ, y₀ ≤ Y →
    ContinuedXiWardMergedSlackSampledScalarLaw (xiWardPrimeLogSampleSet Y)

/-- The same prime-log tail criterion with a three-halves local-margin
allowance at each sample. -/
def ContinuedXiWardPrimeLogTailThreeHalvesSlackLaw : Prop :=
  ∃ y₀ : ℝ, ∀ Y : ℝ, y₀ ≤ Y →
    ContinuedXiWardThreeHalvesSlackSampledScalarLaw (xiWardPrimeLogSampleSet Y)

/-- The source-calibrated prime-log tail criterion with refined allowance
`3C/(log(|t|+9)+1/405)^(9 : ℕ)`, asymptotic to three local margin units. -/
def ContinuedXiWardPrimeLogTailRefinedSlackLaw : Prop :=
  ∃ y₀ : ℝ, ∀ Y : ℝ, y₀ ≤ Y →
    ContinuedXiWardRefinedSlackSampledScalarLaw (xiWardPrimeLogSampleSet Y)

/-- The lowest-burden Ward tail criterion: only the real channel is bounded by
`2 + E(C/(log(|t|+9)+1/405)^(9 : ℕ))`, where
`E(m)=m(1-2m)/(1-3m/2+m²)`, on canonical prime-log samples. -/
def ContinuedXiWardPrimeLogTailRefinedRealLaw : Prop :=
  ∃ y₀ : ℝ, ∀ Y : ℝ, y₀ ≤ Y →
    ContinuedXiWardRefinedSlackSampledRealLaw (xiWardPrimeLogSampleSet Y)

/-- Cofinal rather than eventual prime-log control.  For each requested lower
cutoff, the real law may hold at only one later scale and only on the
nonnegative absolute-value image of its sample set. -/
def ContinuedXiWardPrimeLogCofinalRefinedRealLaw : Prop :=
  ∀ y₀ : ℝ, ∃ Y : ℝ, y₀ ≤ Y ∧
    ContinuedXiWardRefinedSlackSampledRealLaw (abs '' xiWardPrimeLogSampleSet Y)

/-- Minimal one-scale package: one canonical prime-log sample set is already a
detection cover and satisfies the sharp real law on its nonnegative image. -/
def ContinuedXiWardPrimeLogOneCoverRefinedRealLaw : Prop :=
  ∃ Y : ℝ, XiWardDetectionCover (xiWardPrimeLogSampleSet Y) ∧
    ContinuedXiWardRefinedSlackSampledRealLaw (abs '' xiWardPrimeLogSampleSet Y)

/-- Eventual four-unit Gram positivity on canonical prime-log samples. -/
def ContinuedXiWardPrimeLogTailBoundaryGramLaw : Prop :=
  ∃ y₀ : ℝ, ∀ Y : ℝ, y₀ ≤ Y →
    ContinuedXiWardSampledBoundaryGramLaw (xiWardPrimeLogSampleSet Y)

/-- **Premise-discharge reduction.** RH is equivalent to eventual validity of
the four-unit Ward scalar bound on canonical prime-log samples.  Unlike the
generic sampled endpoint, this receiver carries no detection-cover hypothesis. -/
theorem riemannHypothesis_iff_continuedXiWardPrimeLogTailScalarLaw :
    RiemannHypothesis ↔ ContinuedXiWardPrimeLogTailScalarLaw := by
  constructor
  · intro hRH
    obtain ⟨y₀, _hy₀, htail⟩ :=
      exists_cutoff_riemannHypothesis_iff_primeLogSampledScalarLaw
    exact ⟨y₀, fun Y hY => (htail Y hY).mp hRH⟩
  · rintro ⟨y₀, htail⟩
    obtain ⟨y₁, _hy₁, hcover⟩ :=
      exists_cutoff_xiWardDetectionCover_primeLogSampleSet
    apply riemannHypothesis_of_continuedXiWardSampledScalarLaw
      (hcover (max y₀ y₁) (le_max_right _ _))
    exact htail (max y₀ y₁) (le_max_left _ _)

/-- **Lower-burden prime-log endpoint.**  The scalar budget may be relaxed by
the full local zero-free margin at every canonical sample point.  This remains
RH-complete and, like the other tail endpoints, carries no cover premise. -/
theorem riemannHypothesis_iff_continuedXiWardPrimeLogTailMergedSlackLaw :
    RiemannHypothesis ↔ ContinuedXiWardPrimeLogTailMergedSlackLaw := by
  constructor
  · intro hRH
    obtain ⟨y₀, _hy₀, htail⟩ :=
      exists_cutoff_riemannHypothesis_iff_primeLogMergedSlackScalarLaw
    exact ⟨y₀, fun Y hY => (htail Y hY).mp hRH⟩
  · rintro ⟨y₀, htail⟩
    obtain ⟨y₁, _hy₁, hcover⟩ :=
      exists_cutoff_xiWardDetectionCover_primeLogSampleSet
    apply riemannHypothesis_of_continuedXiWardMergedSlackSampledScalarLaw
      (hcover (max y₀ y₁) (le_max_right _ _))
    exact htail (max y₀ y₁) (le_max_left _ _)

/-- **Three-halves-slack prime-log scalar endpoint.**  The sampled four-unit Ward
budget may absorb three halves of the local zero-free margin at every canonical
prime-log node, without restoring a detection-cover premise. -/
theorem riemannHypothesis_iff_continuedXiWardPrimeLogTailThreeHalvesSlackLaw :
    RiemannHypothesis ↔ ContinuedXiWardPrimeLogTailThreeHalvesSlackLaw := by
  constructor
  · intro hRH
    exact ⟨0, fun Y _ =>
      continuedXiWardThreeHalvesSlackSampledScalarLaw_of_riemannHypothesis hRH
        (xiWardPrimeLogSampleSet Y)⟩
  · rintro ⟨y₀, htail⟩
    obtain ⟨y₁, _hy₁, hcover⟩ :=
      exists_cutoff_xiWardDetectionCover_primeLogSampleSet
    apply riemannHypothesis_of_continuedXiWardThreeHalvesSlackSampledScalarLaw
      (hcover (max y₀ y₁) (le_max_right _ _))
    exact htail (max y₀ y₁) (le_max_left _ _)

/-- **Lowest-burden prime-log scalar endpoint.**  Exact detector variation permits the sampled
Ward budget to absorb `3C/(log(|t|+9)+1/405)^(9 : ℕ)`, pointwise more than three halves of the local
margin and asymptotic to three margins, without restoring a cover premise. -/
theorem riemannHypothesis_iff_continuedXiWardPrimeLogTailRefinedSlackLaw :
    RiemannHypothesis ↔ ContinuedXiWardPrimeLogTailRefinedSlackLaw := by
  constructor
  · intro hRH
    exact ⟨0, fun Y _ =>
      continuedXiWardRefinedSlackSampledScalarLaw_of_riemannHypothesis hRH
        (xiWardPrimeLogSampleSet Y)⟩
  · rintro ⟨y₀, htail⟩
    obtain ⟨y₁, _hy₁, hcover⟩ :=
      exists_cutoff_xiWardDetectionCover_primeLogSampleSet
    apply riemannHypothesis_of_continuedXiWardRefinedSlackSampledScalarLaw
      (hcover (max y₀ y₁) (le_max_right _ _))
    exact htail (max y₀ y₁) (le_max_left _ _)

/-- **Lowest-burden prime-log Ward endpoint.**  RH is equivalent to an
eventual two-unit ceiling for only the real Herglotz channel at canonical
prime-log samples.  No imaginary-part or norm-square estimate remains. -/
theorem riemannHypothesis_iff_continuedXiWardPrimeLogTailRefinedRealLaw :
    RiemannHypothesis ↔ ContinuedXiWardPrimeLogTailRefinedRealLaw := by
  constructor
  · intro hRH
    exact ⟨0, fun Y _ =>
      continuedXiWardRefinedSlackSampledRealLaw_of_riemannHypothesis hRH
        (xiWardPrimeLogSampleSet Y)⟩
  · rintro ⟨y₀, htail⟩
    obtain ⟨y₁, _hy₁, hcover⟩ :=
      exists_cutoff_xiWardDetectionCover_primeLogSampleSet
    apply riemannHypothesis_of_continuedXiWardRefinedSlackSampledRealLaw
      (hcover (max y₀ y₁) (le_max_right _ _))
    exact htail (max y₀ y₁) (le_max_left _ _)

/-- Cofinal prime-log real control is enough to intersect the already-proved
eventual detection cover and therefore proves RH. -/
theorem riemannHypothesis_of_continuedXiWardPrimeLogCofinalRefinedRealLaw
    (h : ContinuedXiWardPrimeLogCofinalRefinedRealLaw) :
    RiemannHypothesis := by
  obtain ⟨y₁, _hy₁, hcover⟩ :=
    exists_cutoff_xiWardDetectionCover_primeLogSampleSet
  obtain ⟨Y, hY, hlaw⟩ := h y₁
  exact riemannHypothesis_of_continuedXiWardRefinedSlackSampledRealLaw
    (hcover Y hY)
    ((continuedXiWardRefinedSlackSampledRealLaw_abs_image_iff _).mp hlaw)

/-- **Cofinal one-scale Ward endpoint.**  RH is equivalent to finding, beyond
every lower cutoff, one prime-log sample scale satisfying the sharp refined
real-channel ceiling.  Control at all later scales is unnecessary. -/
theorem riemannHypothesis_iff_continuedXiWardPrimeLogCofinalRefinedRealLaw :
    RiemannHypothesis ↔ ContinuedXiWardPrimeLogCofinalRefinedRealLaw := by
  constructor
  · intro hRH y₀
    exact ⟨y₀, le_rfl,
      continuedXiWardRefinedSlackSampledRealLaw_of_riemannHypothesis hRH
        (abs '' xiWardPrimeLogSampleSet y₀)⟩
  · exact riemannHypothesis_of_continuedXiWardPrimeLogCofinalRefinedRealLaw

/-- One covered prime-log scale with the sharp nonnegative real law proves RH. -/
theorem riemannHypothesis_of_continuedXiWardPrimeLogOneCoverRefinedRealLaw
    (h : ContinuedXiWardPrimeLogOneCoverRefinedRealLaw) :
    RiemannHypothesis := by
  obtain ⟨Y, hcover, hlaw⟩ := h
  exact riemannHypothesis_of_continuedXiWardRefinedSlackSampledRealLaw hcover
    ((continuedXiWardRefinedSlackSampledRealLaw_abs_image_iff _).mp hlaw)

/-- **One-cover Ward endpoint.**  RH is equivalent to the sharp real-channel
ceiling on the nonnegative image of one canonical prime-log sample set whose
cover property is already certified. -/
theorem riemannHypothesis_iff_continuedXiWardPrimeLogOneCoverRefinedRealLaw :
    RiemannHypothesis ↔ ContinuedXiWardPrimeLogOneCoverRefinedRealLaw := by
  constructor
  · intro hRH
    obtain ⟨y₁, _hy₁, hcover⟩ :=
      exists_cutoff_xiWardDetectionCover_primeLogSampleSet
    exact ⟨y₁, hcover y₁ le_rfl,
      continuedXiWardRefinedSlackSampledRealLaw_of_riemannHypothesis hRH
        (abs '' xiWardPrimeLogSampleSet y₁)⟩
  · exact riemannHypothesis_of_continuedXiWardPrimeLogOneCoverRefinedRealLaw

/-- A natural prime-log scale whose detection cover is already certified. -/
def XiWardPrimeLogCertifiedCutoff (N : ℕ) : Prop :=
  3 ≤ N ∧ XiWardDetectionCover (xiWardPrimeLogSampleSet (N : ℝ))

/-- At least one natural prime-log scale has a certified detection cover. -/
theorem exists_xiWardPrimeLogCertifiedCutoff :
    ∃ N : ℕ, XiWardPrimeLogCertifiedCutoff N := by
  obtain ⟨y₁, hy₁, hcover⟩ :=
    exists_cutoff_xiWardDetectionCover_primeLogSampleSet
  obtain ⟨N, hN⟩ := exists_nat_ge y₁
  refine ⟨N, ?_, hcover (N : ℝ) hN⟩
  exact_mod_cast hy₁.trans hN

/-- Least natural prime-log scale whose Ward detection cover is certified. -/
noncomputable def xiWardPrimeLogLeastCertifiedCutoff : ℕ := by
  classical
  exact Nat.find exists_xiWardPrimeLogCertifiedCutoff

theorem xiWardPrimeLogLeastCertifiedCutoff_spec :
    XiWardPrimeLogCertifiedCutoff xiWardPrimeLogLeastCertifiedCutoff := by
  classical
  rw [xiWardPrimeLogLeastCertifiedCutoff]
  exact Nat.find_spec exists_xiWardPrimeLogCertifiedCutoff

theorem xiWardPrimeLogLeastCertifiedCutoff_minimal
    {N : ℕ} (hN : XiWardPrimeLogCertifiedCutoff N) :
    xiWardPrimeLogLeastCertifiedCutoff ≤ N := by
  classical
  rw [xiWardPrimeLogLeastCertifiedCutoff]
  exact Nat.find_min' exists_xiWardPrimeLogCertifiedCutoff hN

/-- **Fixed one-scale Ward endpoint.** RH is exactly the refined real-channel
cap on one fixed, least certified natural prime-log scale. No sample-scale or
detection-cover premise remains. -/
theorem riemannHypothesis_iff_continuedXiWardPrimeLogLeastCertifiedRefinedRealLaw :
    RiemannHypothesis ↔
      ContinuedXiWardRefinedSlackSampledRealLaw
        (abs '' xiWardPrimeLogSampleSet (xiWardPrimeLogLeastCertifiedCutoff : ℝ)) := by
  constructor
  · intro hRH
    exact continuedXiWardRefinedSlackSampledRealLaw_of_riemannHypothesis hRH _
  · intro hlaw
    exact riemannHypothesis_of_continuedXiWardRefinedSlackSampledRealLaw
      xiWardPrimeLogLeastCertifiedCutoff_spec.2
      ((continuedXiWardRefinedSlackSampledRealLaw_abs_image_iff _).mp hlaw)

/-- The matrix endpoint has the same eventual prime-log form as scalar endpoint,
with its detection-cover condition discharged. -/
theorem riemannHypothesis_iff_continuedXiWardPrimeLogTailBoundaryGramLaw :
    RiemannHypothesis ↔ ContinuedXiWardPrimeLogTailBoundaryGramLaw := by
  constructor
  · intro hRH
    obtain ⟨y₀, _hy₀, htail⟩ :=
      exists_cutoff_riemannHypothesis_iff_primeLogSampledBoundaryGramLaw
    exact ⟨y₀, fun Y hY => (htail Y hY).mp hRH⟩
  · rintro ⟨y₀, htail⟩
    obtain ⟨y₁, _hy₁, hcover⟩ :=
      exists_cutoff_xiWardDetectionCover_primeLogSampleSet
    apply riemannHypothesis_of_continuedXiWardSampledBoundaryGramLaw
      (hcover (max y₀ y₁) (le_max_right _ _)).upper
    exact htail (max y₀ y₁) (le_max_left _ _)

/-- Eventual scalar control is equivalent to eventual finite-matrix positivity.
This lets a proof use scalar receiver in place of stronger matrix endpoint. -/
theorem continuedXiWardPrimeLogTailScalarLaw_iff_boundaryGramLaw :
    ContinuedXiWardPrimeLogTailScalarLaw ↔
      ContinuedXiWardPrimeLogTailBoundaryGramLaw :=
  riemannHypothesis_iff_continuedXiWardPrimeLogTailScalarLaw.symm.trans
    riemannHypothesis_iff_continuedXiWardPrimeLogTailBoundaryGramLaw

/-- The margin-relaxed tail law is equivalent to the strict four-unit scalar
tail law, while requiring only the weaker pointwise inequality. -/
theorem continuedXiWardPrimeLogTailScalarLaw_iff_mergedSlackLaw :
    ContinuedXiWardPrimeLogTailScalarLaw ↔
      ContinuedXiWardPrimeLogTailMergedSlackLaw :=
  riemannHypothesis_iff_continuedXiWardPrimeLogTailScalarLaw.symm.trans
    riemannHypothesis_iff_continuedXiWardPrimeLogTailMergedSlackLaw

/-- Three-halves tail control directly supplies refined tail control because the refined allowance
is strictly larger at every prime-log sample. -/
theorem continuedXiWardPrimeLogTailThreeHalvesSlackLaw_implies_refinedSlackLaw
    (h : ContinuedXiWardPrimeLogTailThreeHalvesSlackLaw) :
    ContinuedXiWardPrimeLogTailRefinedSlackLaw := by
  obtain ⟨y₀, htail⟩ := h
  exact ⟨y₀, fun Y hY =>
    continuedXiWardThreeHalvesSlackSampledScalarLaw_implies_refinedSlack (htail Y hY)⟩

/-- Refined norm-square tail control supplies the lower-burden real-channel
tail control at the same cutoff. -/
theorem continuedXiWardPrimeLogTailRefinedSlackLaw_implies_refinedRealLaw
    (h : ContinuedXiWardPrimeLogTailRefinedSlackLaw) :
    ContinuedXiWardPrimeLogTailRefinedRealLaw := by
  obtain ⟨y₀, htail⟩ := h
  exact ⟨y₀, fun Y hY =>
    continuedXiWardRefinedSlackSampledScalarLaw_implies_realLaw (htail Y hY)⟩

/-- Eventual real-channel control implies the strictly weaker cofinal law. -/
theorem continuedXiWardPrimeLogTailRefinedRealLaw_implies_cofinalRealLaw
    (h : ContinuedXiWardPrimeLogTailRefinedRealLaw) :
    ContinuedXiWardPrimeLogCofinalRefinedRealLaw := by
  obtain ⟨y₀, htail⟩ := h
  intro y
  exact ⟨max y y₀, le_max_left _ _,
    (continuedXiWardRefinedSlackSampledRealLaw_abs_image_iff _).mpr
      (htail _ (le_max_right _ _))⟩

/-- Cofinal real control intersects the eventual cover at one scale. -/
theorem continuedXiWardPrimeLogCofinalRefinedRealLaw_implies_oneCoverRealLaw
    (h : ContinuedXiWardPrimeLogCofinalRefinedRealLaw) :
    ContinuedXiWardPrimeLogOneCoverRefinedRealLaw := by
  obtain ⟨y₁, _hy₁, hcover⟩ :=
    exists_cutoff_xiWardDetectionCover_primeLogSampleSet
  obtain ⟨Y, hY, hlaw⟩ := h y₁
  exact ⟨Y, hcover Y hY, hlaw⟩

/-- Canonical consolidation: strict four-unit and refined-slack tail criteria are the same RH
endpoint, while the refined presentation has the weakest source inequality. -/
theorem continuedXiWardPrimeLogTailScalarLaw_iff_refinedSlackLaw :
    ContinuedXiWardPrimeLogTailScalarLaw ↔
      ContinuedXiWardPrimeLogTailRefinedSlackLaw :=
  riemannHypothesis_iff_continuedXiWardPrimeLogTailScalarLaw.symm.trans
    riemannHypothesis_iff_continuedXiWardPrimeLogTailRefinedSlackLaw

/-- Canonical consolidation: the original norm-square law and the refined
real-channel law are the same RH endpoint; the real presentation has the
smallest pointwise source obligation. -/
theorem continuedXiWardPrimeLogTailScalarLaw_iff_refinedRealLaw :
    ContinuedXiWardPrimeLogTailScalarLaw ↔
      ContinuedXiWardPrimeLogTailRefinedRealLaw :=
  riemannHypothesis_iff_continuedXiWardPrimeLogTailScalarLaw.symm.trans
    riemannHypothesis_iff_continuedXiWardPrimeLogTailRefinedRealLaw

/-- Final consolidation: original eventual norm-square tail and cofinal
one-scale real-channel tail are the same RH endpoint.  The cofinal real form
has the smallest quantified source burden. -/
theorem continuedXiWardPrimeLogTailScalarLaw_iff_cofinalRefinedRealLaw :
    ContinuedXiWardPrimeLogTailScalarLaw ↔
      ContinuedXiWardPrimeLogCofinalRefinedRealLaw :=
  riemannHypothesis_iff_continuedXiWardPrimeLogTailScalarLaw.symm.trans
    riemannHypothesis_iff_continuedXiWardPrimeLogCofinalRefinedRealLaw

/-- Canonical consolidation: all earlier Ward tail laws equal the one-cover
real law at RH level; the latter has only one sample-scale obligation. -/
theorem continuedXiWardPrimeLogTailScalarLaw_iff_oneCoverRefinedRealLaw :
    ContinuedXiWardPrimeLogTailScalarLaw ↔
      ContinuedXiWardPrimeLogOneCoverRefinedRealLaw :=
  riemannHypothesis_iff_continuedXiWardPrimeLogTailScalarLaw.symm.trans
    riemannHypothesis_iff_continuedXiWardPrimeLogOneCoverRefinedRealLaw

end RHTower

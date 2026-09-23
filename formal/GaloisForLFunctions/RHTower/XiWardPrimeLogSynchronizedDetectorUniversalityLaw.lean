import GaloisForLFunctions.RHTower.XiWardEdgeMeasurePrimeLogOneNodeSamplingUniversalityLaw
import GaloisForLFunctions.RHTower.XiWardMergedSlackPrimeLogSampling

/-!
# Xi Ward prime-log synchronized-detector universality

The scalar, margin-relaxed scalar, and boundary-Gram prime-log criteria do not merely detect the
same arithmetic phase separately.  On every Ward detection cover, failure of RH has one common
sample at which the relaxed scalar budget is strictly exceeded and the one-node four-unit
boundary Gram is non-positive.  For the locally finite prime-log family, this synchronized
one-node event is exactly nonvanishing of the continuous Ward edge measure.
-/

open Complex Set
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- One sample simultaneously violates the margin-relaxed scalar budget and one-node boundary
Gram positivity. -/
def ContinuedXiWardSynchronizedOneNodeFailure (S : Set ℝ) : Prop :=
  ∃ t ∈ S,
    4 + xiWardZeroFreeMargin t <
      Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) ∧
    ¬ (continuedXiWardFourUnitBoundaryGram
      (fun _ : Fin 1 => (1 / 2 : ℂ) + I * (t : ℂ))).PosSemidef

/-- On any full Ward detection cover, non-RH has a single sample witnessing both strict
margin-relaxed scalar excess and failure of the one-node boundary Gram. -/
theorem not_riemannHypothesis_iff_continuedXiWardSynchronizedOneNodeFailure
    {S : Set ℝ} (hcov : XiWardDetectionCover S) :
    ¬ RiemannHypothesis ↔ ContinuedXiWardSynchronizedOneNodeFailure S := by
  constructor
  · intro hnRH
    obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hnRH
    obtain ⟨t, htS, htwin⟩ := hcov (xiRightCenteredZero q.1).im
    have hm1024 :=
      xiWardZeroFreeMargin_le_inv1024 (xiRightCenteredZero q.1).im
    have hclose : |t + (xiRightCenteredZero q.1).im| ≤ 1 := by
      have hsq : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤ 1 := by
        nlinarith [htwin]
      nlinarith [sq_abs (t + (xiRightCenteredZero q.1).im),
        abs_nonneg (t + (xiRightCenteredZero q.1).im),
        sq_nonneg (|t + (xiRightCenteredZero q.1).im| - 1)]
    have hmargin : xiWardZeroFreeMargin t ≤
        2 * xiWardZeroFreeMargin (xiRightCenteredZero q.1).im :=
      xiWardZeroFreeMargin_close_le_two_mul hclose
    have hexcess :=
      normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four_add q htwin
    exact ⟨t, htS, by linarith,
      continuedXiWardFourUnitBoundaryGram_marginWindow_not_posSemidef q htwin⟩
  · rintro ⟨t, htS, _, hnot⟩ hRH
    have hgram : ContinuedXiWardSampledBoundaryGramLaw S :=
      continuedXiWardSampledBoundaryGramLaw_of_riemannHypothesis hRH S
    exact hnot (hgram (fun _ : Fin 1 => t) (fun _ => htS))

/-- **Prime-log synchronized-detector universality law.**  Beyond one cutoff, vanishing of the
continuous Ward edge measure is exactly simultaneous validity of all three arithmetic sampled
laws.  Nonvanishing is exactly a common one-node witness that defeats both the relaxed scalar
budget and boundary-Gram positivity. -/
theorem exists_cutoff_xiWardEdgeMeasure_primeLogSynchronizedDetectorUniversality :
    ∃ y₁ : ℝ, 3 ≤ y₁ ∧ ∀ Y : ℝ, y₁ ≤ Y →
      (xiWardEdgeMeasure = 0 ↔
        ContinuedXiWardSampledScalarLaw (xiWardPrimeLogSampleSet Y) ∧
        ContinuedXiWardMergedSlackSampledScalarLaw (xiWardPrimeLogSampleSet Y) ∧
        ContinuedXiWardSampledBoundaryGramLaw (xiWardPrimeLogSampleSet Y)) ∧
      (xiWardEdgeMeasure ≠ 0 ↔
        ContinuedXiWardSynchronizedOneNodeFailure
          (xiWardPrimeLogSampleSet Y)) := by
  obtain ⟨y₁, hy₁, hcover⟩ :=
    exists_cutoff_xiWardDetectionCover_primeLogSampleSet
  refine ⟨y₁, hy₁, fun Y hY => ?_⟩
  let S : Set ℝ := xiWardPrimeLogSampleSet Y
  have hcov : XiWardDetectionCover S := hcover Y hY
  have hmeasure :
      RiemannHypothesis ↔ xiWardEdgeMeasure = 0 :=
    riemannHypothesis_iff_xiWardEdgeMeasure_eq_zero
  have hscalar :
      RiemannHypothesis ↔ ContinuedXiWardSampledScalarLaw S :=
    riemannHypothesis_iff_continuedXiWardSampledScalarLaw hcov
  have hslack :
      RiemannHypothesis ↔ ContinuedXiWardMergedSlackSampledScalarLaw S :=
    riemannHypothesis_iff_continuedXiWardMergedSlackSampledScalarLaw hcov
  have hgram :
      RiemannHypothesis ↔ ContinuedXiWardSampledBoundaryGramLaw S :=
    riemannHypothesis_iff_continuedXiWardSampledBoundaryGramLaw hcov.upper
  have hfailure :
      ¬ RiemannHypothesis ↔ ContinuedXiWardSynchronizedOneNodeFailure S :=
    not_riemannHypothesis_iff_continuedXiWardSynchronizedOneNodeFailure hcov
  constructor
  · constructor
    · intro hzero
      have hRH := hmeasure.mpr hzero
      exact ⟨hscalar.mp hRH, hslack.mp hRH, hgram.mp hRH⟩
    · rintro ⟨hscalarLaw, _, _⟩
      exact hmeasure.mp (hscalar.mpr hscalarLaw)
  · constructor
    · intro hne
      apply hfailure.mp
      intro hRH
      exact hne (hmeasure.mp hRH)
    · intro hfail hzero
      exact (hfailure.mpr hfail) (hmeasure.mpr hzero)

end

end RHTower

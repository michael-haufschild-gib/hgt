import GaloisForLFunctions.RHTower.XiWardEdgeMeasureDefect
import GaloisForLFunctions.RHTower.XiWardPrimeLogSampledGramLaw

/-!
# Ward edge-measure prime-log one-node sampling universality

Past one explicit cutoff, the locally finite signed-prime-log sample family is an exact arithmetic
sampler for the continuous Ward edge measure.  Measure vanishing is equivalent to positivity of
every sampled finite boundary Gram, while measure nonvanishing already has a one-node non-PSD
witness at a single arithmetic sample.
-/

open Complex Set
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- One arithmetic height makes the one-node four-unit Ward boundary Gram fail positivity. -/
def ContinuedXiWardOneNodeSampleFailure (S : Set ℝ) : Prop :=
  ∃ t ∈ S,
    ¬ (continuedXiWardFourUnitBoundaryGram
      (fun _ : Fin 1 => (1 / 2 : ℂ) + I * (t : ℂ))).PosSemidef

/-- **Ward edge-measure prime-log one-node sampling law.**  Beyond one cutoff, the continuous
positive Ward measure vanishes exactly when all locally finite arithmetic samples pass the finite
Gram test, and every nonzero measure is detected by one rank-one sampled Gram. -/
theorem exists_cutoff_xiWardEdgeMeasure_primeLogOneNodeSamplingUniversality :
    ∃ y₁ : ℝ, 3 ≤ y₁ ∧ ∀ Y : ℝ, y₁ ≤ Y →
      (xiWardEdgeMeasure = 0 ↔
        ContinuedXiWardSampledBoundaryGramLaw
          (xiWardPrimeLogSampleSet Y)) ∧
      (xiWardEdgeMeasure ≠ 0 ↔
        ContinuedXiWardOneNodeSampleFailure
          (xiWardPrimeLogSampleSet Y)) := by
  obtain ⟨y₁, hy₁, hcover⟩ :=
    exists_cutoff_xiWardDetectionCover_primeLogSampleSet
  refine ⟨y₁, hy₁, fun Y hY => ?_⟩
  let S : Set ℝ := xiWardPrimeLogSampleSet Y
  have hcov : XiWardUpperDetectionCover S :=
    (hcover Y hY).upper
  have hmeasure :
      RiemannHypothesis ↔ xiWardEdgeMeasure = 0 :=
    riemannHypothesis_iff_xiWardEdgeMeasure_eq_zero
  have hlaw :
      RiemannHypothesis ↔ ContinuedXiWardSampledBoundaryGramLaw S :=
    riemannHypothesis_iff_continuedXiWardSampledBoundaryGramLaw hcov
  constructor
  · exact hmeasure.symm.trans hlaw
  · constructor
    · intro hne
      have hnRH : ¬ RiemannHypothesis := by
        intro hRH
        exact hne (hmeasure.mp hRH)
      obtain ⟨q⟩ :=
        nonempty_xiRightUpperZeroCopy_for_boundaryLift hnRH
      obtain ⟨t, htS, htwin⟩ :=
        hcov (xiRightCenteredZero q.1).im q.2
      exact
        ⟨t, htS,
          continuedXiWardFourUnitBoundaryGram_marginWindow_not_posSemidef
            q htwin⟩
    · rintro ⟨t, htS, hnot⟩ hzero
      have hRH : RiemannHypothesis := hmeasure.mpr hzero
      have hsample : ContinuedXiWardSampledBoundaryGramLaw S :=
        continuedXiWardSampledBoundaryGramLaw_of_riemannHypothesis hRH S
      exact hnot
        (hsample (fun _ : Fin 1 => t) (fun _ => htS))

end

end RHTower

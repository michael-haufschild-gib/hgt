import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableFisherHistory
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunablePositiveSource

/-! # Exact positive-source recovery from two normalized observations -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

/-- Literal normalized source equality is exactly equality of the squared ratio parameter. -/
theorem egbFixedChargeAGibbsTunable_normalized_source_eq_iff (t u : ℝ) :
    egbFixedChargeAGibbsTunableNormalizedSource t = egbFixedChargeAGibbsTunableNormalizedSource u ↔
      t ^ 2 = u ^ 2 := by
  constructor
  · intro h
    have hm := congrArg (fun μ : Measure HausdorffSourceSpace => hausdorffMoment μ 0) h
    rw [egbFixedChargeAGibbsTunable_normalized_source_moment,
      egbFixedChargeAGibbsTunable_normalized_source_moment] at hm
    simpa using hm
  · intro h
    have hm : egbFixedChargeAGibbsTunableRatioMass t = egbFixedChargeAGibbsTunableRatioMass u :=
      Subtype.ext h
    unfold egbFixedChargeAGibbsTunableNormalizedSource
    rw [hm]

/-- Across arbitrary grid sizes and attenuations, two successive actual observations classify the normalized source. -/
theorem egbFixedChargeAGibbsTunable_source_eq_iff_two_fisher (n k m p q o : ℕ) (t u : ℝ) :
    egbFixedChargeAGibbsTunableNormalizedSource t = egbFixedChargeAGibbsTunableNormalizedSource u ↔
      (egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
          egbFixedChargeAGibbsCollisionFisherValue p o 1 (egbFixedChargeAGibbsTunableEnergy p q o u) ∧
        egbFixedChargeAGibbsCollisionFisherValue n (m + 1) 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
          egbFixedChargeAGibbsCollisionFisherValue p (o + 1) 1 (egbFixedChargeAGibbsTunableEnergy p q o u)) := by
  rw [egbFixedChargeAGibbsTunable_normalized_source_eq_iff,
    egbFixedChargeAGibbsTunable_fisher_pair_eq_iff]

/-- No additional normalized observations identify anything beyond the source already fixed by the first two. -/
theorem egbFixedChargeAGibbsTunable_fisher_history_eq_iff_source (n k m p q o : ℕ) (t u : ℝ) :
    (∀ j : ℕ, egbFixedChargeAGibbsCollisionFisherValue n (m + j) 1
      (egbFixedChargeAGibbsTunableEnergy n k m t) =
        egbFixedChargeAGibbsCollisionFisherValue p (o + j) 1 (egbFixedChargeAGibbsTunableEnergy p q o u)) ↔
      egbFixedChargeAGibbsTunableNormalizedSource t = egbFixedChargeAGibbsTunableNormalizedSource u := by
  constructor
  · intro h
    apply (egbFixedChargeAGibbsTunable_source_eq_iff_two_fisher n k m p q o t u).2
    exact ⟨by simpa only [Nat.add_zero] using h 0, h 1⟩
  · intro h j
    have hs := (egbFixedChargeAGibbsTunable_normalized_source_eq_iff t u).1 h
    rw [egbFixedChargeAGibbsTunable_fisher_history, egbFixedChargeAGibbsTunable_fisher_history]
    unfold egbFixedChargeAGibbsTunableFisherCurve
    simp only [div_pow, hs]

/-- Two actual readings reconstruct every moment of the literal normalized positive source. -/
theorem egbFixedChargeAGibbsTunable_source_moment_decode (n k m l : ℕ) (t : ℝ) :
    hausdorffMoment (egbFixedChargeAGibbsTunableNormalizedSource t) l =
      (4 / 9 : ℝ) ^ l +
        egbFixedChargeAGibbsFisherRatioDecoder
          (egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t))
          (egbFixedChargeAGibbsCollisionFisherValue n (m + 1) 1 (egbFixedChargeAGibbsTunableEnergy n k m t)) *
        (1 / 36 : ℝ) ^ l := by
  rw [egbFixedChargeAGibbsTunable_fisher_ratio_decode, egbFixedChargeAGibbsTunable_normalized_source_moment]

/-- One-reading ambiguity survives as inequality of actual positive source measures. -/
theorem egbFixedChargeAGibbsTunable_one_fisher_distinct_sources :
    ∃ t u : ℝ, egbFixedChargeAGibbsTunableNormalizedSource t ≠ egbFixedChargeAGibbsTunableNormalizedSource u ∧
      egbFixedChargeAGibbsTunableFisherCurve t = egbFixedChargeAGibbsTunableFisherCurve u := by
  obtain ⟨t, u, _, _, hne, he⟩ := egbFixedChargeAGibbsTunableFisherCurve_reciprocal_ambiguity
  exact ⟨t, u, fun h => hne ((egbFixedChargeAGibbsTunable_normalized_source_eq_iff t u).1 h), he⟩

/-- No function of one Fisher value recovers all positive sources; the two-reading classification is sharp. -/
theorem egbFixedChargeAGibbsTunable_no_one_fisher_source_decoder :
    ¬ ∃ h : ℝ → Measure HausdorffSourceSpace,
      ∀ t : ℝ, h (egbFixedChargeAGibbsTunableFisherCurve t) = egbFixedChargeAGibbsTunableNormalizedSource t := by
  rintro ⟨h, hh⟩
  obtain ⟨t, u, hne, he⟩ := egbFixedChargeAGibbsTunable_one_fisher_distinct_sources
  apply hne
  rw [← hh t, he, hh u]

end
end GaloisForLFunctions.HTGeometry

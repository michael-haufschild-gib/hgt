import GaloisForLFunctions.RHTower.XiWardPrimeLogSampledGramLaw

/-!
# Prime-log tail endpoints for the Xi Ward law

The generic sampled Ward criteria require a proof that the chosen sample set
meets every detection window.  For the canonical prime-log sample family, Lean
already supplies that cover beyond a cutoff.  This module absorbs that side
condition into two closed endpoint criteria and shows that eventual scalar
control is equivalent to eventual finite-matrix positivity.
-/

namespace RHTower

/-- The canonical prime-log Ward scalar estimate need only hold eventually;
the arithmetic detection-cover side condition is discharged inside endpoint. -/
def ContinuedXiWardPrimeLogTailScalarLaw : Prop :=
  ∃ y₀ : ℝ, ∀ Y : ℝ, y₀ ≤ Y →
    ContinuedXiWardSampledScalarLaw (xiWardPrimeLogSampleSet Y)

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

end RHTower

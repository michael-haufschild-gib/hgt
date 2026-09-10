import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeBoundaryIntegrals

/-! # A nonzero positive source survives exact dimensional rescaling -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

/-- Positive grid size as a scalar acting on finite measures. -/
def egbFixedChargeAGibbsSpikeGridMass (n : ℕ) : NNReal :=
  ⟨(2 : ℝ) ^ (n + 3), by positivity⟩

def egbFixedChargeAGibbsSpikeRescaledSlowMass (o : ℕ) : NNReal :=
  ⟨(4 / 9 : ℝ) ^ (o + 1) / 2, by positivity⟩

def egbFixedChargeAGibbsSpikeRescaledFastMass (o : ℕ) : NNReal :=
  ⟨(1 / 36 : ℝ) ^ (o + 1) / 2, by positivity⟩

/-- The two retained atoms after scaling away their vanishing dimensional amplitude. -/
def egbFixedChargeAGibbsSpikeRescaledSource (o : ℕ) : Measure HausdorffSourceSpace :=
  hausdorffAtomSource (egbFixedChargeAGibbsSpikeRescaledSlowMass o) egbFixedChargeAGibbsCollisionSlowNode +
  hausdorffAtomSource (egbFixedChargeAGibbsSpikeRescaledFastMass o) egbFixedChargeAGibbsCollisionFastNode

instance (o : ℕ) : IsFiniteMeasure (egbFixedChargeAGibbsSpikeRescaledSource o) := by
  unfold egbFixedChargeAGibbsSpikeRescaledSource
  infer_instance

/-- The entire positive-time measure, at every offset, is recovered by one exact positive rescaling. -/
theorem egbFixedChargeAGibbsSpike_rescaled_source_eq (n o : ℕ) :
    egbFixedChargeAGibbsSpikeGridMass n •
      egbFixedChargeAGibbsCollisionHausdorffSource n o 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      egbFixedChargeAGibbsSpikeRescaledSource o := by
  have hr : egbFixedChargeAGibbsSpikeGridMass n *
      egbFixedChargeAGibbsCollisionSlowSourceMass n o 1 (egbFixedChargeAGibbsSpikeEnergy n) =
        egbFixedChargeAGibbsSpikeRescaledSlowMass o := by
    apply Subtype.ext
    change (2 : ℝ) ^ (n + 3) * ((4 / 9 : ℝ) ^ (o + 1) *
      egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n)) = (4 / 9 : ℝ) ^ (o + 1) / 2
    rw [egbFixedChargeAGibbsSpike_slow_energy]
    have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [hn]
    <;> ring
  have hs : egbFixedChargeAGibbsSpikeGridMass n *
      egbFixedChargeAGibbsCollisionFastSourceMass n o 1 (egbFixedChargeAGibbsSpikeEnergy n) =
        egbFixedChargeAGibbsSpikeRescaledFastMass o := by
    apply Subtype.ext
    change (2 : ℝ) ^ (n + 3) * ((1 / 36 : ℝ) ^ (o + 1) *
      egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n)) = (1 / 36 : ℝ) ^ (o + 1) / 2
    rw [egbFixedChargeAGibbsSpike_fast_energy]
    have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [hn]
    <;> ring
  simp only [egbFixedChargeAGibbsCollisionHausdorffSource, egbFixedChargeAGibbsSpikeRescaledSource,
    hausdorffAtomSource, smul_add, smul_smul, hr, hs]

/-- Every moment of the positive survivor is the exact rescaled collision observation. -/
theorem egbFixedChargeAGibbsSpike_rescaled_source_moment (n o m : ℕ) :
    hausdorffMoment (egbFixedChargeAGibbsSpikeRescaledSource o) m =
      (2 : ℝ) ^ (n + 3) *
        egbFixedChargeAGibbsCollisionExcess n (m + o + 1) 1 (egbFixedChargeAGibbsSpikeEnergy n) := by
  rw [← egbFixedChargeAGibbsSpike_rescaled_source_eq n o]
  unfold hausdorffMoment
  rw [integral_smul_nnreal_measure]
  change (2 : ℝ) ^ (n + 3) *
    hausdorffMoment (egbFixedChargeAGibbsCollisionHausdorffSource n o 1 (egbFixedChargeAGibbsSpikeEnergy n)) m = _
  rw [egbFixedChargeAGibbsCollisionHausdorffSource_moment]

/-- The surviving positive source has an explicit dimension-free moment sequence. -/
theorem egbFixedChargeAGibbsSpike_rescaled_source_moment_formula (o m : ℕ) :
    hausdorffMoment (egbFixedChargeAGibbsSpikeRescaledSource o) m =
      ((4 / 9 : ℝ) ^ (m + o + 1) + (1 / 36 : ℝ) ^ (m + o + 1)) / 2 := by
  rw [egbFixedChargeAGibbsSpike_rescaled_source_moment 0 o m,
    egbFixedChargeAGibbsSpike_rescaled_positive_collision]

/-- Each observation of the rescaled positive source remains strictly positive. -/
theorem egbFixedChargeAGibbsSpike_rescaled_source_moment_pos (o m : ℕ) :
    0 < hausdorffMoment (egbFixedChargeAGibbsSpikeRescaledSource o) m := by
  rw [egbFixedChargeAGibbsSpike_rescaled_source_moment_formula]
  positivity

/-- The positive source recovered from the vanishing sector is never the zero measure. -/
theorem egbFixedChargeAGibbsSpike_rescaled_source_ne_zero (o : ℕ) :
    egbFixedChargeAGibbsSpikeRescaledSource o ≠ 0 := by
  intro h
  have hp := egbFixedChargeAGibbsSpike_rescaled_source_moment_pos o 0
  simp [h, hausdorffMoment] at hp

end
end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.FrequencyEvent

/-! # A derivative-order upper tail on each fixed coupling box -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
open SpectralJets PrescribedTimes.ResonantDraws.PlateauConfidence
noncomputable section

/-- Total power of the confidence parameter in the spectral margin. -/
def marginOrder (k : ℕ) : ℕ := prefixDetectorDegree k+(2^(k+3)-2)

/-- Phase-filling deadline on a box at unit confidence parameter. -/
def boxDeadline (k : ℕ) (T : ℝ) : ℝ :=
  phaseClockPrice k/confidenceMargin k (retainedClockModes k).card T 1

theorem boxDeadline_pos (k : ℕ) (T : ℝ) : 0 < boxDeadline k T := by
  dsimp only [boxDeadline,phaseClockPrice,confidenceMargin]
  positivity

theorem deadline_factor (k : ℕ) (T η : ℝ) :
    phaseClockPrice k/confidenceMargin k (retainedClockModes k).card T η =
      boxDeadline k T*(η^(marginOrder k))⁻¹ := by
  simp only [boxDeadline,confidenceMargin,marginOrder,div_eq_mul_inv,mul_inv_rev,←inv_pow,
    inv_inv,pow_add,mul_pow,one_mul]
  ring

/-- If all physical couplings lie in the box, a long first excursion
forces a small retained frequency. Its mass is at most twice the target
confidence parameter. The bound also controls every smaller wait. -/
theorem gaussian_local_passage_tail :
    ∀ᶠ k : ℕ in atTop, ∀ T η : ℝ, 0≤T → 0<η → η≤1 →
      let n := k+1
      let μ := Measure.pi fun _ : PrescribedTimes.PrefixIndex n => gaussianReal 0 1
      μ.real {x | (∀ i, |x i| ≤ T) ∧ boxDeadline k T*(η^marginOrder k)⁻¹ < passageMax k 0 x}
        ≤ 2*η := by
  filter_upwards [passage_tail_on_event] with k hk
  intro T η hT hη hη' n μ
  let S := retainedClockModes k
  let δ := confidenceMargin k S.card T η
  let K := {x : PrescribedTimes.PrefixIndex n → ℝ | ∀ i, |x i|≤T}
  have hbox : MeasurableSet K := by
    change MeasurableSet {x : PrescribedTimes.PrefixIndex n → ℝ | ∀ i, |x i|≤T}
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i).abs measurable_const
  have hδ : 0<δ := by dsimp only [δ,confidenceMargin]; positivity
  have hle := (hk K hbox 0 δ hδ).trans (gaussian_box_margin k S hT hη hη')
  rw [←ENNReal.ofReal_add hη.le hη.le] at hle
  rw [←deadline_factor]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans
    ((ENNReal.toReal_ofReal (add_nonneg hη.le hη.le)).le.trans_eq (two_mul η).symm)

#print axioms gaussian_local_passage_tail
end
end GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds

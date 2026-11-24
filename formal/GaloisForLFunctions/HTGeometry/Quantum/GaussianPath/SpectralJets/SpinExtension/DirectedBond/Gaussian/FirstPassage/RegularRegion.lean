import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.FirstPassage.Detuning
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.FrequencyEvent

/-! # First-excursion tails where the physical spectral determinant is separated from zero -/
open Matrix MvPolynomial Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
open PrescribedTimes PassageMoments PassageMoments.DerivativeBounds
noncomputable section

private theorem continuous_detector_size (N L : ℕ) (rows : Fin (2^N)→Option (List (Coordinates N))) :
    Continuous (fun θ : Coordinates N→ℝ => ‖eval₂Hom GaussianInt.toComplex
      (fun a => (θ a:ℂ)) (pathDetector N L rows)‖) := by
  let Q := map GaussianInt.toComplex (pathDetector N L rows)
  have he : (fun θ : Coordinates N→ℝ => ‖eval₂Hom GaussianInt.toComplex
      (fun a => (θ a:ℂ)) (pathDetector N L rows)‖) = fun θ => ‖eval (realEmbed θ) Q‖ := by
    funext θ
    exact congrArg norm (eval_map ..).symm
  rw [he]
  exact (Q.continuous_eval.comp continuous_realEmbed).norm

/-- On a coupling box with a fixed positive determinant floor, the failure
probability is linear in r at a first-excursion deadline proportional to r⁻ᴸ.
The same determinant works for every budget and every floor. -/
theorem directed_regular_region_tail :
    ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let L := 2*(k+2)+1
      ∃ rows : Fin (2^N)→Option (List (Coordinates N)),
        map GaussianInt.toComplex (pathDetector N L rows)≠0 ∧
        ∀ (s : ℕ) (T κ r : ℝ), 0≤T → 0<κ → κ≤1 → 0<r → r≤1 →
          let μ := Measure.pi fun _ : Coordinates N => gaussianReal 0 1
          let a := κ/(1+|pathResponseCap N L T*(2^N:ℕ)|)
          μ {θ | (∀ i, |θ i|≤T) ∧ κ≤‖eval₂Hom GaussianInt.toComplex (fun i => (θ i:ℂ))
            (pathDetector N L rows)‖ ∧ phaseClockPrice k/(a*r^L)<passageMax k s θ} ≤
            ENNReal.ofReal ((modeStripPrice (2^N) L (retainedClockModes k).card:ℝ)*r) := by
  filter_upwards [passage_tail_on_event] with k hk
  intro N L
  obtain ⟨rows,hw,hn,_,_⟩ := low_order_detector_tail (k+2)
  refine ⟨rows,hn,?_⟩
  intro s T κ r hT hκ hκ' hr hr' μ a
  let S := {θ : Coordinates N→ℝ | (∀ i, |θ i|≤T) ∧
    κ≤‖eval₂Hom GaussianInt.toComplex (fun i => (θ i:ℂ)) (pathDetector N L rows)‖}
  have hb : MeasurableSet {θ : Coordinates N→ℝ | ∀ i, |θ i|≤T} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i).abs measurable_const
  have hS : MeasurableSet S := hb.inter
    (measurableSet_le measurable_const (continuous_detector_size N L rows).measurable)
  have ha : 0<a := div_pos hκ (by positivity)
  have he := hk S hS s (a*r^L) (mul_pos ha (pow_pos hr _))
  have h₁ := measure_mono (μ:=μ) (show {θ | (∀ i, |θ i|≤T) ∧
      κ≤‖eval₂Hom GaussianInt.toComplex (fun i => (θ i:ℂ)) (pathDetector N L rows)‖ ∧
      phaseClockPrice k/(a*r^L)<passageMax k s θ} ⊆ S ∩ {θ | phaseClockPrice k/(a*r^L)<passageMax k s θ} from
    fun _ h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩)
  apply (h₁.trans he).trans
  apply (measure_mono ?_).trans (box_detuning_above_detector N L rows hw (retainedClockModes k) hT hκ hκ' hr hr')
  exact fun _ h => ⟨h.1.1,h.1.2,h.2⟩

#print axioms directed_regular_region_tail
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond

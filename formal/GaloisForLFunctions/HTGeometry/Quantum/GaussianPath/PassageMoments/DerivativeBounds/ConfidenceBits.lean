import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.DyadicTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.PhaseClock

/-! # Quantiles at every bit of first-passage confidence -/
open Set Filter MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
open PrescribedTimes SpectralJets
noncomputable section

/-- One extra bit of confidence costs at most the detector-plus-jet order
in log₂ deadline, simultaneously in prefix size and confidence. -/
theorem gaussian_first_passage_confidence_bits :
    ∃ c : ℕ, ∀ᶠ k : ℕ in atTop, ∀ u : ℕ,
      let D : ℕ := 2^(k+3)
      let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
      μ.real {x | (2:ℝ)^(D^c+u*marginOrder k)<passageMax k 0 x}
        ≤ (8/3)*(1/2:ℝ)^(D+u) := by
  obtain ⟨c,hc⟩ := calibrated_confidence_horizon
  refine ⟨c,?_⟩
  filter_upwards [gaussian_derivative_survival] with k hk u
  intro D μ
  let d := marginOrder k
  let A := boxDeadline k (confidenceBox k)
  have hbase : A*((2:ℝ)^d)^D ≤ (2:ℝ)^(D^c) := by
    have h := hc k
    change phaseClockPrice k/confidenceMargin k (retainedClockModes k).card (confidenceBox k)
      ((1/2:ℝ)^D) ≤ (2:ℝ)^(D^c) at h
    rwa [deadline_factor,dyadic_margin_inverse] at h
  have hg : A*((2:ℝ)^d)^(D+u) ≤ (2:ℝ)^(D^c+u*d) := calc
    _ = (A*((2:ℝ)^d)^D)*((2:ℝ)^d)^u := by rw [pow_add,mul_assoc]
    _ ≤ (2:ℝ)^(D^c)*((2:ℝ)^d)^u := mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = _ := by rw [pow_add,Nat.mul_comm u d,pow_mul (2:ℝ) d u]
  have hh := hk 0 ((1/2:ℝ)^(D+u)) (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  rw [dyadic_margin_inverse] at hh
  exact (measureReal_mono (μ:=μ) (show {x | (2:ℝ)^(D^c+u*d)<passageMax k 0 x} ⊆
    {x | A*((2:ℝ)^d)^(D+u)<passageMax k 0 x} from fun _ h => hg.trans_lt h)).trans hh

#print axioms gaussian_first_passage_confidence_bits
end
end GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds

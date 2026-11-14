import GaloisForLFunctions.HilbertMetric.QuantumInformation.TwoModeTemporalSampling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Arbitrarily short exact observations resolve two fermion modes

For a positive energy gap, an explicit sampling time smaller than any prescribed
exponential scale gives two distinct phases. The exact two-mode observed space
is therefore already full and its compression entropy is zero. Coincident
samples instead leave a one-dimensional space with entropy `log 2`.
This distinguishes exact finite-dimensional temporal spans from numerical
singular-value cutoffs in continuum-time sampling.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric
open Real

/-- Time evolution of the second mode relative to a zero-energy first mode. -/
def twoModeEvolutionPhase (q t : ℝ) : ℂ :=
  Complex.exp ((exp q * t : ℝ) * Complex.I)

/-- A separating observation time, smaller than `exp(-s)` for every real `s`. -/
def twoModeSeparatingTime (q s : ℝ) : ℝ := 1 / (exp q + exp s)

theorem twoModeSeparatingTime_pos (q s : ℝ) : 0 < twoModeSeparatingTime q s := by
  unfold twoModeSeparatingTime
  positivity

theorem twoModeSeparatingTime_lt (q s : ℝ) : twoModeSeparatingTime q s < exp (-s) := by
  rw [twoModeSeparatingTime, exp_neg]
  simpa only [one_div] using
    one_div_lt_one_div_of_lt (exp_pos s) (by linarith [exp_pos q])

/-- The explicit short sample has phase angle strictly between zero and one. -/
theorem twoModeSeparatingTime_phaseAngle (q s : ℝ) :
    0 < exp q * twoModeSeparatingTime q s ∧ exp q * twoModeSeparatingTime q s < 1 := by
  constructor
  · exact mul_pos (exp_pos q) (twoModeSeparatingTime_pos q s)
  · unfold twoModeSeparatingTime
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith [exp_pos s]

/-- The short-time second phase cannot collide with the first phase. -/
theorem twoModeSeparatingTime_no_alias (q s : ℝ) :
    (1 : ℂ) ≠ twoModeEvolutionPhase q (twoModeSeparatingTime q s) := by
  have hangle := twoModeSeparatingTime_phaseAngle q s
  have hsin := sin_pos_of_pos_of_le_one hangle.1 hangle.2.le
  intro h
  have hi := congrArg Complex.im h
  simp [twoModeEvolutionPhase, Complex.exp_im] at hi
  linarith

/-- Exact two-mode entropy vanishes at the explicitly separated short time. -/
theorem twoModeSeparatingTime_entropy (q s : ℝ) :
    fermionSpectralEntropy (twoModeTemporalCorrelation 1
      (twoModeEvolutionPhase q (twoModeSeparatingTime q s))) = 0 := by
  rw [twoModeTemporalCorrelation_entropy, if_neg (twoModeSeparatingTime_no_alias q s)]

/-- Coincident samples retain one full bit of fermion entropy. -/
theorem twoModeEvolutionPhase_zero_entropy (q : ℝ) :
    fermionSpectralEntropy (twoModeTemporalCorrelation 1 (twoModeEvolutionPhase q 0)) =
      Real.log 2 := by
  simp [twoModeEvolutionPhase, twoModeTemporalCorrelation_entropy]

/-- Every prescribed positive time scale contains an exact pure observed space. -/
theorem twoMode_arbitrarily_short_pure (q s : ℝ) :
    ∃ t : ℝ, 0 < t ∧ t < exp (-s) ∧
      fermionSpectralEntropy (twoModeTemporalCorrelation 1 (twoModeEvolutionPhase q t)) = 0 :=
  ⟨twoModeSeparatingTime q s, twoModeSeparatingTime_pos q s,
    twoModeSeparatingTime_lt q s, twoModeSeparatingTime_entropy q s⟩

/-- Exact observed-space entropy jumps at coincident sampling times. This is a
rank discontinuity, before any numerical singular-value cutoff is introduced. -/
theorem twoModeTemporalEntropy_not_continuousAt_zero (q : ℝ) :
    ¬ ContinuousAt (fun t => fermionSpectralEntropy
      (twoModeTemporalCorrelation 1 (twoModeEvolutionPhase q t))) 0 := by
  intro hc
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc (Real.log 2 / 2) (by positivity)
  have ht := twoModeSeparatingTime_lt q (-Real.log δ)
  rw [neg_neg, Real.exp_log hδ] at ht
  have hd : dist (twoModeSeparatingTime q (-Real.log δ)) 0 < δ := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_pos (twoModeSeparatingTime_pos q (-Real.log δ))] using ht
  have hbad := hclose hd
  rw [twoModeSeparatingTime_entropy, twoModeEvolutionPhase_zero_entropy,
    Real.dist_eq, zero_sub, abs_neg, abs_of_pos hlog] at hbad
  linarith only [hbad, hlog]

end GaloisForLFunctions.HilbertMetric

-- BEGIN PAPER AXIOM AUDIT
#print axioms GaloisForLFunctions.HilbertMetric.twoModeSeparatingTime_pos
#print axioms GaloisForLFunctions.HilbertMetric.twoModeSeparatingTime_lt
#print axioms GaloisForLFunctions.HilbertMetric.twoModeSeparatingTime_phaseAngle
#print axioms GaloisForLFunctions.HilbertMetric.twoModeSeparatingTime_no_alias
#print axioms GaloisForLFunctions.HilbertMetric.twoModeSeparatingTime_entropy
#print axioms GaloisForLFunctions.HilbertMetric.twoModeEvolutionPhase_zero_entropy
#print axioms GaloisForLFunctions.HilbertMetric.twoMode_arbitrarily_short_pure
#print axioms GaloisForLFunctions.HilbertMetric.twoModeTemporalEntropy_not_continuousAt_zero
-- END PAPER AXIOM AUDIT

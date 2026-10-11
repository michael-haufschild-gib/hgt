import GaloisForLFunctions.RHTower.WeilLogShiftJointWeakLimit

/-! Every real projection converges, including the collapsed anti-diagonal direction. -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section
namespace RHTower

def finiteWeilCanonicalProjectedProbabilityLaw (r k : ℕ) (a b : ℝ) : ProbabilityMeasure ℝ :=
  finiteWeilCanonicalObservableLaw r k (fun i =>
    (a * (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) +
      b * (((r + 1 : ℕ) : ℝ) *
        (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k))) /
      Real.sqrt ((r + 1 : ℕ) : ℝ))

def finiteWeilProjectedGaussian (a b : ℝ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (NNReal.mk ((a + b) ^ 2 / 4) (by positivity)), inferInstance⟩

theorem finiteWeilCanonicalProjectedProbabilityLaw_charFun (r k : ℕ) (a b u : ℝ) :
    charFun (finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ) u =
      finiteWeilCanonicalJointCharacteristic r k (u * a) (u * b) := by
  rw [finiteWeilCanonicalProjectedProbabilityLaw, charFun_apply_real,
    finiteWeilCanonicalObservableLaw_integral_complex]
  unfold finiteWeilCanonicalJointCharacteristic finiteWeilPhase
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  push_cast
  ring

theorem finiteWeilProjectedGaussian_charFun (a b u : ℝ) :
    charFun (finiteWeilProjectedGaussian a b : Measure ℝ) u =
      (Real.exp (-((u * a + u * b) ^ 2 / 8)) : ℂ) := by
  change charFun (gaussianReal 0 (NNReal.mk ((a + b) ^ 2 / 4) (by positivity))) u = _
  rw [charFun_gaussianReal, Complex.ofReal_exp]
  push_cast
  congr 1
  ring

theorem tendsto_finiteWeilCanonicalProjectedProbabilityLaw_gaussian (t : ℕ → ℕ) (a b : ℝ) :
    Tendsto (fun r => finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) a b)
      atTop (𝓝 (finiteWeilProjectedGaussian a b)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro u
  simp_rw [finiteWeilCanonicalProjectedProbabilityLaw_charFun, finiteWeilProjectedGaussian_charFun]
  exact tendsto_finiteWeilCanonicalJointCharacteristic_gaussian t (u * a) (u * b)

theorem tendsto_finiteWeilCanonicalProjectedProbabilityLaw_antidiagonal (t : ℕ → ℕ) (a : ℝ) :
    Tendsto (fun r => finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) a (-a))
      atTop (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  simpa [finiteWeilProjectedGaussian, gaussianReal_zero_var] using
    tendsto_finiteWeilCanonicalProjectedProbabilityLaw_gaussian t a (-a)

end RHTower
